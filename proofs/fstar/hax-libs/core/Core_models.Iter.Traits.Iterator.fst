module Core_models.Iter.Traits.Iterator

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

(* f_rev and f_collect *)
assume val f_rev : #v_I:Type0 -> {| i: t_IteratorMethods v_I |} -> v_I
  -> Core_models.Iter.Adapters.Rev.t_Rev v_I

assume val f_collect : #v_I:Type0 -> {| i: t_IteratorMethods v_I |}
  -> #v_B:Type0 -> v_I -> v_B

assume val f_copied : #v_I:Type0 -> {| i: t_IteratorMethods v_I |} -> #v_Item:Type0 -> v_I
  -> Core_models.Iter.Adapters.Copied.t_Copied v_I

assume val f_find : #v_I:Type0 -> {| i: t_IteratorMethods v_I |}
  -> #v_P:Type0 -> #v_Item:Type0
  -> v_I -> v_P
  -> (v_I & Core_models.Option.t_Option v_Item)

(* NOTE: IntoIterator for Vec is in Golden_dkg.Iter_instances.fst to avoid
   circular dependency: Iterator -> Alloc.Vec -> Iterator *)

(* --- t_Iterator instances moved from Slice.Iter.fst --- *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_slice_iter_is_iterator (#v_T: Type0)
  : t_Iterator (Core_models.Slice.Iter.t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun _ -> true);
    f_next_post = (fun _ _ -> true);
    f_next = (fun self ->
      let Core_models.Slice.Iter.Iter s = self in
      if (Rust_primitives.Sequence.seq_len #v_T s <: usize) =. mk_usize 0
      then (self, Core_models.Option.Option_None)
      else
        let res = Rust_primitives.Sequence.seq_first #v_T s in
        let new_s = Rust_primitives.Sequence.seq_slice #v_T s (mk_usize 1) (Rust_primitives.Sequence.seq_len #v_T s) in
        (Core_models.Slice.Iter.Iter new_s, Core_models.Option.Option_Some res))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_chunks_is_iterator (v_T: Type0)
  : t_Iterator (Core_models.Slice.Iter.t_Chunks v_T)

(* --- t_Iterator instances from Range (concrete, with f_Item) --- *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_range_u32_is_iterator : t_Iterator (Core_models.Ops.Range.t_Range u32) =
  { f_Item = u32;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_range_usize_is_iterator : t_Iterator (Core_models.Ops.Range.t_Range usize) =
  { f_Item = usize;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

(* RangeInclusive yields the same item type as Range *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_range_inclusive_u32_is_iterator
  : t_Iterator (Core_models.Ops.Range.t_RangeInclusive u32) =
  { f_Item = u32;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_range_inclusive_usize_is_iterator
  : t_Iterator (Core_models.Ops.Range.t_RangeInclusive usize) =
  { f_Item = usize;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

(* --- IteratorMethods instances ---
   These use `admit()` for bodies but provide CONCRETE `_super_i0` with known `f_Item`,
   which is critical for f_fold's FnOnce typeclass resolution. *)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_slice_iter (#v_T: Type0)
  : t_IteratorMethods (Core_models.Slice.Iter.t_Iter v_T) =
  { _super_i0 = impl_slice_iter_is_iterator #v_T;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* Concrete Rev instance for Slice.Iter -- F* needs to see f_Item = v_T *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_rev_slice_iter (#v_T: Type0)
  : t_IteratorMethods (Core_models.Iter.Adapters.Rev.t_Rev (Core_models.Slice.Iter.t_Iter v_T)) =
  { _super_i0 = { f_Item = v_T;
                   f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
                   f_next = (fun _ -> admit ()) };
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* f_filter and f_copied *)
assume val f_filter : #v_I:Type0 -> {| i: t_IteratorMethods v_I |}
  -> #v_P:Type0 -> v_I -> v_P
  -> Core_models.Iter.Adapters.Filter.t_Filter v_I v_P

assume val f_copied : #v_I:Type0 -> {| i: t_IteratorMethods v_I |} -> v_I
  -> Core_models.Iter.Adapters.Copied.t_Copied v_I

(* --- HashMap iterator instances (concrete, with f_Item specified) --- *)

(* HashMap::Iter yields (K & V) pairs *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_hashmap_iter (#v_K #v_V: Type0)
  : t_Iterator (Std.Collections.Hash.Map.t_Iter v_K v_V) =
  { f_Item = (v_K & v_V);
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_hashmap_iter (#v_K #v_V: Type0)
  : t_IteratorMethods (Std.Collections.Hash.Map.t_Iter v_K v_V) =
  { _super_i0 = impl_iterator_hashmap_iter;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* HashMap::Keys yields K values *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_hashmap_keys (#v_K #v_V: Type0)
  : t_Iterator (Std.Collections.Hash.Map.t_Keys v_K v_V) =
  { f_Item = v_K;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_hashmap_keys (#v_K #v_V: Type0)
  : t_IteratorMethods (Std.Collections.Hash.Map.t_Keys v_K v_V) =
  { _super_i0 = impl_iterator_hashmap_keys;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* HashMap::Values yields V values *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_hashmap_values (#v_K #v_V: Type0)
  : t_Iterator (Std.Collections.Hash.Map.t_Values v_K v_V) =
  { f_Item = v_V;
    f_next_pre = (fun _ -> true); f_next_post = (fun _ _ -> true);
    f_next = (fun _ -> admit ()) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_hashmap_values (#v_K #v_V: Type0)
  : t_IteratorMethods (Std.Collections.Hash.Map.t_Values v_K v_V) =
  { _super_i0 = impl_iterator_hashmap_values;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* HashMap IntoIterator instance -- yields (K & V) pairs *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_hashmap (#v_K #v_V #v_S: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Std.Collections.Hash.Map.t_HashMap v_K v_V v_S)

(* Filter/Copied iterator instances *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_filter (v_I v_P: Type0)
  : t_IteratorMethods (Core_models.Iter.Adapters.Filter.t_Filter v_I v_P)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_filter (v_I v_P: Type0)
  : t_Iterator (Core_models.Iter.Adapters.Filter.t_Filter v_I v_P)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_copied (v_I: Type0)
  : t_IteratorMethods (Core_models.Iter.Adapters.Copied.t_Copied v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_copied (v_I: Type0)
  : t_Iterator (Core_models.Iter.Adapters.Copied.t_Copied v_I)

(* Generic Rev instance for other iterator types *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_rev (v_I: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_map (v_I: Type0) (v_F: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (Core_models.Iter.Bundle.t_Map v_I v_F)

(* RangeInclusive<u32> IteratorMethods with concrete f_Item = u32 *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_range_inclusive_u32
  : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive u32) =
  { _super_i0 = impl_range_inclusive_u32_is_iterator;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* RangeInclusive<usize> IteratorMethods *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_range_inclusive_usize
  : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive usize) =
  { _super_i0 = impl_range_inclusive_usize_is_iterator;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* Range<u32> IteratorMethods *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_range_u32
  : t_IteratorMethods (Core_models.Ops.Range.t_Range u32) =
  { _super_i0 = impl_range_u32_is_iterator;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* Range<usize> IteratorMethods *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_iterator_methods_range_usize
  : t_IteratorMethods (Core_models.Ops.Range.t_Range usize) =
  { _super_i0 = impl_range_usize_is_iterator;
    f_fold_pre = (fun #_ #_ #_ #_ _ _ _ -> true);
    f_fold_post = (fun #_ #_ #_ #_ _ _ _ _ -> true);
    f_fold = (fun #_ #_ #_ #_ _ init _ -> admit ());
    f_enumerate_pre = (fun _ -> true); f_enumerate_post = (fun _ _ -> true); f_enumerate = (fun _ -> admit ());
    f_step_by_pre = (fun _ _ -> true); f_step_by_post = (fun _ _ _ -> true); f_step_by = (fun _ _ -> admit ());
    f_map_pre = (fun #_ #_ _ _ -> true); f_map_post = (fun #_ #_ _ _ _ -> true); f_map = (fun #_ #_ _ _ -> admit ());
    f_all_pre = (fun #_ _ _ -> true); f_all_post = (fun #_ _ _ _ -> true); f_all = (fun #_ _ _ -> admit ());
    f_take_pre = (fun _ _ -> true); f_take_post = (fun _ _ _ -> true); f_take = (fun _ _ -> admit ());
    f_flat_map_pre = (fun #_ #_ _ _ -> true); f_flat_map_post = (fun #_ #_ _ _ _ -> true); f_flat_map = (fun #_ #_ _ _ -> admit ());
    f_flatten_pre = (fun _ -> true); f_flatten_post = (fun _ _ -> true); f_flatten = (fun _ -> admit ());
    f_zip_pre = (fun #_ _ _ -> true); f_zip_post = (fun #_ _ _ _ -> true); f_zip = (fun #_ _ _ -> admit ());
  }

(* IntoIterator instances *)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_rev (v_I: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_map (v_I: Type0) (v_F: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Core_models.Iter.Bundle.t_Map v_I v_F)
