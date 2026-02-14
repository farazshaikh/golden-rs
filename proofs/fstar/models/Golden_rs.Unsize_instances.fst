module Golden_rs.Unsize_instances

/// Blanket unsize instance for types that don't have specific coercions.
/// In --lax mode, this allows any type to be "unsized" to any target.

open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_unsize_blanket (#v_S: Type0) : unsize_tc v_S
