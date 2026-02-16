module Fold.Axioms

/// Axioms about fold_enumerated_slice, which is an opaque `assume val`
/// in Rust_primitives.Hax.Folds.fsti.
///
/// fold_range is a `let rec` and F* can unfold it directly, so no axioms
/// are needed for it. But fold_enumerated_slice cannot be unfolded, so
/// we axiomatize its behavior here.
///
/// All extracted hax code uses the trivial invariant `(fun _ _ -> true)`,
/// so our axioms are specialized to that case. This avoids the difficulty
/// of stating axioms over arbitrary invariants where intermediate `inv`
/// obligations can't be discharged.
///
/// These axioms are SOUND under the assumption that fold_enumerated_slice
/// is implemented as a left-fold over the slice, which matches the Rust
/// semantics of `for (i, item) in slice.iter().enumerate() { ... }`.

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// The trivial invariant used in all hax-extracted fold_enumerated_slice calls.
let trivial_inv (#acc_t : Type0) (#s_len : nat)
  : acc_t -> (i:usize{v i <= s_len}) -> Type0
  = fun _ _ -> True

// ============================================================================
// fold_enumerated_slice axioms (specialized to trivial invariant)
// ============================================================================

/// Axiom: fold_enumerated_slice over an empty slice returns init.
assume val fold_enumerated_slice_empty :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 0)
    (ensures
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == init)

/// Axiom: fold_enumerated_slice over a 1-element slice applies f once.
assume val fold_enumerated_slice_one :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 1)
    (ensures (
      let item0 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 0, Seq.index s 0) in
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == f init item0))

/// Axiom: fold_enumerated_slice over a 2-element slice applies f twice.
assume val fold_enumerated_slice_two :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 2)
    (ensures (
      let item0 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 0, Seq.index s 0) in
      let acc1 = f init item0 in
      let item1 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 1, Seq.index s 1) in
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == f acc1 item1))

/// Axiom: fold_enumerated_slice over a 3-element slice applies f three times.
assume val fold_enumerated_slice_three :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 3)
    (ensures (
      let item0 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 0, Seq.index s 0) in
      let acc1 = f init item0 in
      let item1 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 1, Seq.index s 1) in
      let acc2 = f acc1 item1 in
      let item2 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 2, Seq.index s 2) in
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == f acc2 item2))

/// Axiom: fold_enumerated_slice over a 4-element slice applies f four times.
assume val fold_enumerated_slice_four :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 4)
    (ensures (
      let item0 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 0, Seq.index s 0) in
      let acc1 = f init item0 in
      let item1 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 1, Seq.index s 1) in
      let acc2 = f acc1 item1 in
      let item2 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 2, Seq.index s 2) in
      let acc3 = f acc2 item2 in
      let item3 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 3, Seq.index s 3) in
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == f acc3 item3))

/// Axiom: fold_enumerated_slice over a 5-element slice applies f five times.
assume val fold_enumerated_slice_five :
  #t:Type0 -> #acc_t:Type0 ->
  s:t_Slice t ->
  init:acc_t ->
  f:(acc:acc_t -> i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i))}
             -> acc_t) ->
  Lemma
    (requires Seq.length s == 5)
    (ensures (
      let item0 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 0, Seq.index s 0) in
      let acc1 = f init item0 in
      let item1 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 1, Seq.index s 1) in
      let acc2 = f acc1 item1 in
      let item2 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 2, Seq.index s 2) in
      let acc3 = f acc2 item2 in
      let item3 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 3, Seq.index s 3) in
      let acc4 = f acc3 item3 in
      let item4 : (x:(usize & t){v (fst x) < v (length s) /\ snd x == Seq.index s (v (fst x))}) =
        (sz 4, Seq.index s 4) in
      Rust_primitives.Hax.Folds.fold_enumerated_slice s
        (fun (_:acc_t) (_:usize{v _ <= Seq.length s}) -> True)
        init
        (fun (acc:acc_t) (i:(usize & t){v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ True})
         -> f acc i)
      == f acc4 item4))
