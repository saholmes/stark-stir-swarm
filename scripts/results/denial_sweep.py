import subprocess, random, re, csv, sys
from concurrent.futures import ThreadPoolExecutor

DOMAINS = "/Volumes/SAHexternal 1/Documents/stark-stir-swarm/scripts/data/se-domains-tranco.txt"
OUT     = "/private/tmp/claude-501/-Volumes-SAHexternal-1-Documents/ae4e919f-b95a-4294-a0c8-1ea326df4fab/scratchpad/denial_sweep_results.csv"
SUMMARY = "/private/tmp/claude-501/-Volumes-SAHexternal-1-Documents/ae4e919f-b95a-4294-a0c8-1ea326df4fab/scratchpad/denial_sweep_summary.txt"
TYPES = ["A","AAAA","MX","TXT","NS","SOA","CAA","HTTPS"]  # common client query types
SAMPLE = 1000

doms = [l.strip() for l in open(DOMAINS) if l.strip()]
random.seed(20260627)
sample = random.sample(doms, min(SAMPLE, len(doms)))

def dig(name, qtype):
    try:
        out = subprocess.run(["dig","+nocmd","+time=2","+tries=1",qtype,name],
                             capture_output=True, text=True, timeout=6).stdout
    except Exception:
        return ("ERROR", 0)
    m_s = re.search(r"status:\s*([A-Z]+)", out)
    m_a = re.search(r"ANSWER:\s*(\d+)", out)
    return (m_s.group(1) if m_s else "ERROR", int(m_a.group(1)) if m_a else 0)

def classify(status, ans):
    if status == "NXDOMAIN": return "NXDOMAIN"
    if status == "NOERROR":  return "POSITIVE" if ans > 0 else "NODATA"
    return "OTHER"

jobs = [(d,t) for d in sample for t in TYPES]
# NXDOMAIN probe: one random non-existent label per domain
jobs += [("nx-zq7v9k2."+d, "A") for d in sample]

rows = []
def work(j):
    name, t = j
    st, ans = dig(name, t)
    return (name, t, st, ans, classify(st, ans))

with ThreadPoolExecutor(max_workers=24) as ex:
    for r in ex.map(work, jobs):
        rows.append(r)

with open(OUT,"w",newline="") as f:
    w=csv.writer(f); w.writerow(["name","qtype","status","answer_count","class"]); w.writerows(rows)

# aggregate
existing = [r for r in rows if not r[0].startswith("nx-zq7v9k2.")]
nxprobe  = [r for r in rows if r[0].startswith("nx-zq7v9k2.")]
from collections import Counter
by_class = Counter(r[4] for r in existing)
per_type = {}
for t in TYPES:
    sub=[r for r in existing if r[1]==t]
    c=Counter(r[4] for r in sub)
    per_type[t]=(c.get("POSITIVE",0), c.get("NODATA",0), len(sub))
tot = len(existing)
pos = by_class.get("POSITIVE",0); nod = by_class.get("NODATA",0)
nx_ok = sum(1 for r in nxprobe if r[4]=="NXDOMAIN")

with open(SUMMARY,"w") as f:
    f.write(f"Denial-of-existence structural sweep — .se Tranco, seed=20260627\n")
    f.write(f"Sample: {len(sample)} existing names x {len(TYPES)} types = {tot} (name,type) queries\n\n")
    f.write(f"Among EXISTING names (name,type) queries:\n")
    f.write(f"  POSITIVE (answer present): {pos} ({100*pos/tot:.1f}%)\n")
    f.write(f"  NODATA   (name exists, type absent -> needs denial): {nod} ({100*nod/tot:.1f}%)\n")
    for k in ("NXDOMAIN","OTHER","ERROR"):
        if by_class.get(k): f.write(f"  {k}: {by_class[k]} ({100*by_class[k]/tot:.1f}%)\n")
    f.write(f"\nNXDOMAIN probe (random non-existent label per name):\n")
    f.write(f"  NXDOMAIN returned: {nx_ok}/{len(nxprobe)} ({100*nx_ok/max(1,len(nxprobe)):.1f}%)\n")
    f.write(f"\nPer-type among existing names (POSITIVE / NODATA / total):\n")
    for t in TYPES:
        p,n,tt=per_type[t]
        f.write(f"  {t:6s}: pos={p:4d} nodata={n:4d}  -> NODATA {100*n/max(1,tt):.0f}%\n")
print(open(SUMMARY).read())
