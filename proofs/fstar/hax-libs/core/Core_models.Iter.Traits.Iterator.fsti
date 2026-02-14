module Core_models.Iter.Traits.Iterator

/// PATCHED: .fsti interface that breaks the circular dependency
/// between Iterator <-> Slice.Iter.
///
/// This file re-exports the t_Iterator typeclass and t_IteratorMethods
/// from Bundle WITHOUT depending on Slice.Iter.
///
/// Slice.Iter.fst depends on this .fsti (not the .fst), so the cycle is broken:
///   .fsti (typeclass defs) <-- Slice.Iter.fst (provides instances)
///   .fst (re-exports instances) --> Slice.Iter.fst
///
/// See: formal_verification/Implementation.md "hax Proof-Lib Patches"

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

(* --- t_Iterator typeclass --- *)
include Core_models.Iter.Bundle {t_Iterator as t_Iterator}
include Core_models.Iter.Bundle {f_Item as f_Item}
include Core_models.Iter.Bundle {f_next_pre as f_next_pre}
include Core_models.Iter.Bundle {f_next_post as f_next_post}
include Core_models.Iter.Bundle {f_next as f_next}

(* --- t_IteratorMethods typeclass --- *)
include Core_models.Iter.Bundle {t_IteratorMethods as t_IteratorMethods}
(* f_fold: simplified signature without FnOnce constraint for --lax mode. *)
val f_fold : #v_I:Type0 -> {| t_IteratorMethods v_I |}
  -> #v_B:Type0 -> #v_F:Type0
  -> v_I -> v_B -> v_F
  -> v_B
include Core_models.Iter.Bundle {f_enumerate_pre as f_enumerate_pre}
include Core_models.Iter.Bundle {f_enumerate_post as f_enumerate_post}
include Core_models.Iter.Bundle {f_enumerate as f_enumerate}
include Core_models.Iter.Bundle {f_step_by_pre as f_step_by_pre}
include Core_models.Iter.Bundle {f_step_by_post as f_step_by_post}
include Core_models.Iter.Bundle {f_step_by as f_step_by}
(* f_map: simplified signature without FnOnce constraint for --lax mode.
   The Bundle version requires t_FnOnce which can't resolve through opaque .fsti instances. *)
val f_map : #v_I:Type0 -> {| t_IteratorMethods v_I |}
  -> #v_B:Type0 -> #v_F:Type0
  -> v_I -> v_F
  -> Core_models.Iter.Bundle.t_Map v_I v_F
(* f_all: simplified *)
val f_all : #v_I:Type0 -> {| t_IteratorMethods v_I |} -> #v_F:Type0 -> v_I -> v_F -> bool
include Core_models.Iter.Bundle {f_take_pre as f_take_pre}
include Core_models.Iter.Bundle {f_take_post as f_take_post}
include Core_models.Iter.Bundle {f_take as f_take}
include Core_models.Iter.Bundle {f_flat_map_pre as f_flat_map_pre}
include Core_models.Iter.Bundle {f_flat_map_post as f_flat_map_post}
include Core_models.Iter.Bundle {f_flat_map as f_flat_map}
include Core_models.Iter.Bundle {f_flatten_pre as f_flatten_pre}
include Core_models.Iter.Bundle {f_flatten_post as f_flatten_post}
include Core_models.Iter.Bundle {f_flatten as f_flatten}
include Core_models.Iter.Bundle {f_zip_pre as f_zip_pre}
include Core_models.Iter.Bundle {f_zip_post as f_zip_post}
include Core_models.Iter.Bundle {f_zip as f_zip}
include Core_models.Iter.Bundle {impl as impl}
include Core_models.Iter.Bundle {impl_1__from__iterator as impl_1}

(* --- Missing methods needed by golden-rs extraction --- *)
val f_rev : #v_I:Type0 -> {| i: t_IteratorMethods v_I |} -> v_I
  -> Core_models.Iter.Adapters.Rev.t_Rev v_I

val f_collect : #v_I:Type0 -> {| i: t_IteratorMethods v_I |}
  -> #v_B:Type0 -> v_I -> v_B

val f_filter : #v_I:Type0 -> {| i: t_IteratorMethods v_I |}
  -> #v_P:Type0 -> v_I -> v_P
  -> Core_models.Iter.Adapters.Filter.t_Filter v_I v_P

val f_copied : #v_I:Type0 -> {| i: t_IteratorMethods v_I |} -> v_I
  -> Core_models.Iter.Adapters.Copied.t_Copied v_I

(* --- t_Iterator instances moved from Slice.Iter and Range --- *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_slice_iter_is_iterator (#v_T: Type0)
  : t_Iterator (Core_models.Slice.Iter.t_Iter v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_chunks_is_iterator (v_T: Type0)
  : t_Iterator (Core_models.Slice.Iter.t_Chunks v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_range_u32_is_iterator : t_Iterator (Core_models.Ops.Range.t_Range u32)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_range_usize_is_iterator : t_Iterator (Core_models.Ops.Range.t_Range usize)

(* --- IteratorMethods instances (must be in .fsti for typeclass resolution) --- *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_rev (v_I: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_map (v_I: Type0) (v_F: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (Core_models.Iter.Bundle.t_Map v_I v_F)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_range_inclusive (v_T: Type0)
  : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_slice_iter (v_T: Type0)
  : t_IteratorMethods (Core_models.Slice.Iter.t_Iter v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_into_iter_rev (v_I: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_into_iter_map (v_I: Type0) (v_F: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Core_models.Iter.Bundle.t_Map v_I v_F)

(* --- HashMap/Filter/Copied/Range iterator instances are defined in .fst --- *)
(* They are concrete (with visible f_Item) so f_fold/f_map FnOnce resolution works. *)
(* The .fsti declares them as val so dependent modules can see them. *)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_hashmap_iter (v_K v_V: Type0) : t_Iterator (Std.Collections.Hash.Map.t_Iter v_K v_V)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_hashmap_iter (v_K v_V: Type0) : t_IteratorMethods (Std.Collections.Hash.Map.t_Iter v_K v_V)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_hashmap_keys (v_K v_V v_S: Type0) : t_Iterator (Std.Collections.Hash.Map.t_Keys v_K v_V v_S)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_hashmap_keys (v_K v_V v_S: Type0) : t_IteratorMethods (Std.Collections.Hash.Map.t_Keys v_K v_V v_S)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_hashmap_values (v_K v_V v_S: Type0) : t_Iterator (Std.Collections.Hash.Map.t_Values v_K v_V v_S)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_hashmap_values (v_K v_V v_S: Type0) : t_IteratorMethods (Std.Collections.Hash.Map.t_Values v_K v_V v_S)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_into_iter_hashmap (v_K v_V v_S: Type0) : Core_models.Iter.Traits.Collect.t_IntoIterator (Std.Collections.Hash.Map.t_HashMap v_K v_V v_S)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_filter (v_I v_P: Type0) : t_Iterator (Core_models.Iter.Adapters.Filter.t_Filter v_I v_P)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_filter (v_I v_P: Type0) : t_IteratorMethods (Core_models.Iter.Adapters.Filter.t_Filter v_I v_P)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_copied (v_I: Type0) : t_Iterator (Core_models.Iter.Adapters.Copied.t_Copied v_I)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_copied (v_I: Type0) : t_IteratorMethods (Core_models.Iter.Adapters.Copied.t_Copied v_I)

(* Range instances with concrete f_Item visible in .fsti *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_range_inclusive_u32_is_iterator : t_Iterator (Core_models.Ops.Range.t_RangeInclusive u32)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_range_inclusive_u32 : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive u32)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_range_inclusive_usize_is_iterator : t_Iterator (Core_models.Ops.Range.t_RangeInclusive usize)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_range_inclusive_usize : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive usize)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_range_u32 : t_IteratorMethods (Core_models.Ops.Range.t_Range u32)
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_iterator_methods_range_usize : t_IteratorMethods (Core_models.Ops.Range.t_Range usize)
