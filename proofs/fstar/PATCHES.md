# hax Proof-Library Patches for Golden DKG

This document describes the patches applied to hax's F* proof-libs to enable
lax-checking of the extracted golden-rs modules.

## Setup Instructions

```bash
# 1. Build hax from source (see formal_verification/Implementation.md)
# 2. Vendor the proof-libs into the project:
mkdir -p proofs/fstar/hax-libs/{core,rust_primitives,hax_lib}
cp -r /tmp/hax-build/proof-libs/fstar/core/* proofs/fstar/hax-libs/core/
cp -r /tmp/hax-build/proof-libs/fstar/rust_primitives/* proofs/fstar/hax-libs/rust_primitives/
cp /tmp/hax-build/hax-lib/proofs/fstar/extraction/*.fst proofs/fstar/hax-libs/hax_lib/
# 3. Apply the patches below.
```

## Patch 1: Break Iterator <-> Slice.Iter Circular Dependency

**Problem:** `Core_models.Iter.Traits.Iterator.fst` and `Core_models.Slice.Iter.fst` have a
mutual dependency (Iterator re-exports Slice.Iter, Slice.Iter provides Iterator instances).
F* error 308 (fatal recursive dependency).

**Fix:** The `.fsti` sandwich pattern.

1. **Create** `core/Core_models.Iter.Traits.Iterator.fsti` -- re-exports the typeclass
   definitions from Bundle WITHOUT depending on Slice.Iter. Declares `f_rev`, `f_collect`,
   and all IteratorMethods/IntoIterator instances as `val`.

2. **Replace** `core/Core_models.Iter.Traits.Iterator.fst` -- implementation provides
   `f_rev`/`f_collect` as `assume val`, concrete `t_Iterator` instance for `Slice.Iter`,
   and `assume val` IteratorMethods instances. The `.fst` depends on Slice.Iter but the
   `.fsti` does NOT, breaking the cycle.

3. **Replace** `core/Core_models.Slice.Iter.fst` -- remove all `[@@ tcinstance]` declarations
   (the `t_Iterator` instances for `t_Iter`, `t_Chunks`, `t_ChunksExact`). Keep only type
   definitions and constructors. The moved instances now live in Iterator.fst.

## Patch 2: Break Iterator <-> Range Circular Dependency

**Problem:** Same pattern -- `Core_models.Ops.Range.fst` provides `t_Iterator` instances
for Range types, creating a cycle with Iterator.

**Fix:** Strip `Range.fst` down to type definitions only (t_Range, t_RangeTo, t_RangeFrom,
t_RangeFull, t_RangeInclusive). Move the 12 `t_Iterator` instances to Iterator.fst as
`assume val`.

## Patch 3: Add t_RangeInclusive

**Problem:** `Core_models.Ops.Range.fst` does not define `t_RangeInclusive`, which is needed
by the extracted `for i in 1..=n` pattern.

**Fix:** Add to Range.fst:
```fstar
type t_RangeInclusive (v_T: Type0) = { f_start: v_T; f_end_inclusive: v_T; }
let impl_7__new (#v_T: Type0) (start end_val: v_T) : t_RangeInclusive v_T = ...
```

## Patch 4: Add Rand.Rng.t_Rng Typeclass

**Problem:** `Rand.Rng.fsti` in hax core is empty (just the module declaration).
The extracted code references `Rand.Rng.t_Rng`.

**Fix:** Replace `core/Rand.Rng.fsti` with:
```fstar
module Rand.Rng
class t_Rng (v_Self : Type0) = { __rng_dummy : unit; }
```

## Verification Command

```bash
FSTAR=~/.local/fstar/fstar/bin/fstar.exe
$FSTAR --lax --warn_error -331 \
  --include proofs/fstar/models \
  --include proofs/fstar/extraction \
  --include proofs/fstar/hax-libs/core \
  --include proofs/fstar/hax-libs/rust_primitives \
  --include proofs/fstar/hax-libs/hax_lib \
  proofs/fstar/extraction/Golden_rs.Shamir.fst
```

Expected output: `All verification conditions discharged successfully`
