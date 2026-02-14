module Core_models.Iter.Adapters.Copied
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Opaque Copied iterator adapter type.
/// Copied<I> wraps an iterator I that yields &T and yields T by copying.
assume new type t_Copied (v_I: Type0) : Type0
