#!/usr/bin/env python3
"""DNS-STARK sliver-proving wall-clock SIMULATOR — measure-once / simulate-many.

Reads per-strand costs (costs.json, measured in isolation on ONE machine) and a
workload DAG, then simulates list-scheduling across P processors with a communication
model to estimate the PARALLEL prove wall-clock — WITHOUT owning P processors.

Sound because the sliver architecture makes strand PROOFS independent (the witness is a
cheap serial precompute): the only things that change with P are queueing (the scheduler
models it exactly) and communication (calibrated) — no new memory contention appears
across separate processors/devices. Calibrate the comm params at small P against a real
parallel run, then extrapolate.

Usage:
    python3 sim.py --workload rsa2048 --limb 256
    python3 sim.py --workload epoch:100 --limb 64 --net iot
    python3 sim.py --workload rsa2048 --p 1,64,1024,16384 --net dc
    python3 sim.py --workload epoch:1000 --scheme mixed --net iot --edge proof
"""
import argparse
import heapq
import json
import math
import os


class Task:
    __slots__ = ("id", "cost", "out", "deps")

    def __init__(self, tid, cost, out, deps):
        self.id = tid
        self.cost = float(cost)   # prove_ms on one node
        self.out = int(out)       # bytes transferred to dependents
        self.deps = deps          # list of task ids


# ----------------------------------------------------------------------------- costs
def load_costs(path):
    with open(path) as f:
        return json.load(f)


def strand(costs, key):
    s = costs["strands"].get(key)
    if s is None:
        raise SystemExit(f"unknown strand '{key}' — have: {', '.join(costs['strands'])}")
    return s


# ------------------------------------------------------------------- workload DAGs
# Each workload returns (tasks: dict[id]->Task, root_id). Aggregation edges carry the
# 32-byte root by default; pass edge_bytes=<leaf proof size> to model Tier-B recursion
# (the master consumes the inner proof).

def _agg_tree(tasks, leaves, join, arity, edge_bytes, tag):
    """Build a k-ary aggregation tree of join nodes over `leaves`; return the root id."""
    level = leaves
    j = 0
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), arity):
            group = level[i:i + arity]
            tid = f"{tag}_j{j}"
            j += 1
            tasks[tid] = Task(tid, join["prove_ms"], edge_bytes, list(group))
            nxt.append(tid)
        level = nxt
    return level[0] if level else None


def workload_rsa2048(costs, limb_key, arity, edge_bytes, tag="rsa"):
    """One RSA-2048 record verify, slivered. e=65537 => 17 ModMul<8192>; each ModMul is
    limb-decomposed into 2*k^2 limb strands (k=2048/L) for the a*b and q*N grids. All
    strand proofs are independent leaves; aggregate to a record root."""
    tasks = {}
    lp = strand(costs, limb_key)
    join = strand(costs, "join_aggregation")
    L = int(limb_key.rsplit("_", 1)[1])
    k = 2048 // L
    strands_per_modmul = 2 * k * k
    n_modmul = 17  # 16 squarings + 1 multiply
    leaves = []
    for i in range(n_modmul * strands_per_modmul):
        tid = f"{tag}_lp{i}"
        tasks[tid] = Task(tid, lp["prove_ms"], edge_bytes, [])
        leaves.append(tid)
    root = _agg_tree(tasks, leaves, join, arity, edge_bytes, tag)
    return tasks, root, {"leaves": len(leaves), "leaf": limb_key, "n_modmul": n_modmul,
                         "strands_per_modmul": strands_per_modmul, "leaf_proof_bytes": lp["proof_bytes"]}


def _scheme_leaf_count(costs, scheme, limb_key):
    """(#leaf strands, strand key, per-leaf note) for one record of a scheme."""
    if scheme == "rsa2048":
        L = int(limb_key.rsplit("_", 1)[1]); k = 2048 // L
        return 17 * 2 * k * k, limb_key
    if scheme == "ed25519":
        return 894, "dblstrand_ed25519"       # ~510 doublings + ~383 adds + decision
    if scheme == "ecdsa":
        return 513, "wdblfull_ecdsa"           # ~512 doublings (adds not yet gated)
    if scheme == "mldsa":
        return 32400, "keccakf_mldsa"          # ~32k atomic circuits, Keccak-f RSS-peak
    raise SystemExit(f"unknown scheme '{scheme}'")


def workload_flat(n, cost_ms, out_bytes=0):
    """N independent strands, no aggregation — the calibration workload (embarrassingly
    parallel; makespan = ceil(N/P)*cost under the ideal no-contention model)."""
    tasks = {f"s{i}": Task(f"s{i}", cost_ms, out_bytes, []) for i in range(n)}
    return tasks, None, {"leaves": n, "leaf": "flat", "leaf_proof_bytes": 0}


def workload_epoch(costs, n_records, scheme, limb_key, arity, edge_bytes):
    """An N-record epoch: each record's strands are leaves; per-record roots aggregate
    into a zone/epoch root (the published epoch artifact)."""
    tasks = {}
    join = strand(costs, "join_aggregation")
    nleaf, skey = _scheme_leaf_count(costs, scheme, limb_key)
    lp = strand(costs, skey)
    record_roots = []
    total_leaves = 0
    for r in range(n_records):
        leaves = []
        for s in range(nleaf):
            tid = f"e{r}_lp{s}"
            tasks[tid] = Task(tid, lp["prove_ms"], edge_bytes, [])
            leaves.append(tid)
        total_leaves += nleaf
        rroot = _agg_tree(tasks, leaves, join, arity, edge_bytes, f"e{r}")
        record_roots.append(rroot)
    root = _agg_tree(tasks, record_roots, join, arity, edge_bytes, "epoch")
    return tasks, root, {"leaves": total_leaves, "records": n_records, "scheme": scheme,
                         "leaf": skey, "leaf_proof_bytes": lp["proof_bytes"]}


# ------------------------------------------------------------- comm + scheduler
def comm_ms(nbytes, latency_ms, bw_bytes_per_ms):
    return latency_ms + nbytes / bw_bytes_per_ms if nbytes > 0 else 0.0


def schedule(tasks, P, latency_ms, bw):
    """Discrete-event list-scheduler. Returns (makespan_ms, util_frac, busy_ms)."""
    n = len(tasks)
    dependents = {i: [] for i in tasks}
    remaining = {}
    for i, t in tasks.items():
        remaining[i] = len(t.deps)
        for d in t.deps:
            dependents[d].append(i)
    ready_time = {i: 0.0 for i in tasks}
    ready = []  # (ready_time, id)
    for i, t in tasks.items():
        if not t.deps:
            heapq.heappush(ready, (0.0, i))
    running = []  # (finish, id)
    free = P
    now = 0.0
    makespan = 0.0
    busy = 0.0
    done = 0
    while done < n:
        while ready and free > 0 and ready[0][0] <= now + 1e-9:
            rt, i = heapq.heappop(ready)
            fin = max(now, rt) + tasks[i].cost
            heapq.heappush(running, (fin, i))
            free -= 1
            busy += tasks[i].cost
        cand = []
        if running:
            cand.append(running[0][0])
        if ready and free > 0:
            cand.append(ready[0][0])   # a ready task still waiting on its ready_time
        if not cand:
            if not running:
                break
            cand.append(running[0][0])
        now = min(cand)
        while running and running[0][0] <= now + 1e-9:
            fin, i = heapq.heappop(running)
            free += 1
            done += 1
            makespan = max(makespan, fin)
            av = fin + comm_ms(tasks[i].out, latency_ms, bw)
            for d in dependents[i]:
                ready_time[d] = max(ready_time[d], av)
                remaining[d] -= 1
                if remaining[d] == 0:
                    heapq.heappush(ready, (ready_time[d], d))
    util = busy / (P * makespan) if makespan > 0 else 0.0
    return makespan, util, busy


NETS = {  # latency_ms, bandwidth bytes/ms
    "dc":  (0.1, 1_000_000.0),     # datacenter fleet: 100us + ~1 GB/s
    "lan": (1.0, 125_000.0),       # LAN: 1ms + ~1 Gbit/s
    "iot": (30.0, 1_000.0),        # IoT/WAN fleet: 30ms RTT + ~1 MB/s
}


def fmt_ms(ms):
    if ms < 1000:
        return f"{ms:.0f} ms"
    s = ms / 1000
    if s < 90:
        return f"{s:.1f} s"
    m = s / 60
    if m < 90:
        return f"{m:.1f} min"
    return f"{m/60:.2f} h"


def main():
    ap = argparse.ArgumentParser(description="DNS-STARK sliver-proving parallel wall-clock simulator")
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--costs", default=os.path.join(here, "costs.json"))
    ap.add_argument("--workload", default="rsa2048", help="rsa2048 | epoch:N")
    ap.add_argument("--scheme", default="rsa2048", help="epoch scheme: rsa2048|ed25519|ecdsa|mldsa")
    ap.add_argument("--limb", default="256", help="RSA limb size L (64|128|256)")
    ap.add_argument("--arity", type=int, default=2, help="aggregation tree arity")
    ap.add_argument("--net", default="dc", choices=list(NETS), help="communication model")
    ap.add_argument("--edge", default="root", choices=["root", "proof"],
                    help="aggregation edge transfer: 32-byte root (Tier-A) or full proof (Tier-B recursion)")
    ap.add_argument("--p", default="1,8,64,512,4096,16384", help="comma-separated processor counts")
    ap.add_argument("--strand-cost-ms", type=float, default=None,
                    help="override per-strand cost (for calibration flat:N workload)")
    args = ap.parse_args()

    costs = load_costs(args.costs)
    limb_key = f"limbproduct_{args.limb}"
    edge_root = costs["comm_edge_bytes"]["aggregation_root"]

    if args.workload.startswith("flat:"):
        n = int(args.workload.split(":", 1)[1])
        cost = args.strand_cost_ms if args.strand_cost_ms is not None else strand(costs, limb_key)["prove_ms"]
        tasks, root, info = workload_flat(n, cost)
        title = f"FLAT {n} strands (calibration)"
    elif args.workload.startswith("epoch:"):
        n = int(args.workload.split(":", 1)[1])
        _, skey = _scheme_leaf_count(costs, args.scheme, limb_key)
        edge_bytes = strand(costs, skey)["proof_bytes"] if args.edge == "proof" else edge_root
        tasks, root, info = workload_epoch(costs, n, args.scheme, limb_key, args.arity, edge_bytes)
        title = f"EPOCH ({n} × {args.scheme})"
    else:
        edge_bytes = strand(costs, limb_key)["proof_bytes"] if args.edge == "proof" else edge_root
        tasks, root, info = workload_rsa2048(costs, limb_key, args.arity, edge_bytes, )
        title = "RSA-2048 record (slivered)"

    lat, bw = NETS[args.net]
    ntasks = len(tasks)
    serial = sum(t.cost for t in tasks.values())
    depth = int(math.ceil(math.log(max(info["leaves"], 2), args.arity)))
    # critical path (P = inf) — the wall-clock floor no fleet size beats
    cp_ms, _, _ = schedule(tasks, ntasks, lat, bw)

    print(f"# DNS-STARK sliver simulator — {title}")
    print(f"# leaves={info['leaves']:,}  join-nodes={ntasks - info['leaves']:,}  total-tasks={ntasks:,}  "
          f"agg-depth={depth}  arity={args.arity}")
    print(f"# net={args.net} (latency={lat}ms, bw={bw/1000:.0f} KB/ms)  edge={args.edge}  "
          f"leaf={info['leaf']}")
    print(f"# serial (1 proc) total compute = {fmt_ms(serial)}   critical-path floor = {fmt_ms(cp_ms)}")
    print()
    print(f"| {'processors':>10} | {'wall-clock':>11} | {'speedup':>8} | {'util':>6} | {'vs critical-path':>16} |")
    print(f"|{'-'*12}|{'-'*13}|{'-'*10}|{'-'*8}|{'-'*18}|")
    for p in [int(x) for x in args.p.split(",")]:
        ms, util, _ = schedule(tasks, p, lat, bw)
        sp = serial / ms if ms > 0 else 0
        over = ms / cp_ms if cp_ms > 0 else 1
        print(f"| {p:>10,} | {fmt_ms(ms):>11} | {sp:>7.1f}× | {util*100:>5.0f}% | {over:>15.2f}× |")
    print()
    print(f"# The critical-path floor ({fmt_ms(cp_ms)}) = one strand + {depth} aggregation levels — "
          f"the wall-clock no number of processors beats.")


if __name__ == "__main__":
    main()
