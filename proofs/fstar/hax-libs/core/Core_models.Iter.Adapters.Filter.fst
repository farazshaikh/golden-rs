module Core_models.Iter.Adapters.Filter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Opaque Filter iterator adapter type.
/// Filter<I, P> wraps an iterator I with a predicate P.
assume new type t_Filter (v_I: Type0) (v_P: Type0) : Type0
