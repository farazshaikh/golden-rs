# Simplex Consensus -- Formal Verification

This directory will contain Lean 4 / Hax proofs for the Simplex consensus core.

## Verification target

- `src/replica.rs` -- the state machine logic
- `src/types.rs` -- data structures
- `src/vrf.rs` -- leader election

## Reference papers

- Chan & Pass 2023, "Simplex Consensus" (eprint.iacr.org/2023/463)
- Shoup 2025, "DispersedSimplex" (eprint.iacr.org/2023/1916)
