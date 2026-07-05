# binius-substrate — provenance & license

This crate is **original work**: the binary-field STARK prototype demonstrating
NIST L1/L3/L5 security over a binary-tower Binius — the 256- and 512-bit tower
fields (`b256_field`, `b512_field`), their packed subfield layers, in-circuit
SHA3-256/384/512, and the sound recursion bindings (padding-binding, digest seam,
root boundary, cross-table channel join).

It depends, via **path dependencies**, on a fork of **Binius**
(Apache License 2.0, Copyright Irreducible Inc.). The changes made to that fork
are recorded in the fork's `MODIFICATIONS.md` and satisfy Apache-2.0 Section 4(b);
the stock `2^128` Binius path is unchanged.

This crate is licensed under the **Apache License, Version 2.0**, for consistency
with the Binius dependency. See the Binius fork's `LICENSE.txt` for the full
license text. Retained upstream attribution ("Irreducible Inc.") credits the
Binius authors, not the authors of this crate.
