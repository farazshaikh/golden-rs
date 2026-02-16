module Golden_dkg.Iter_instances

/// Additional typeclass instances for iterator adapters used by golden-rs.
/// These are blanket instances that enable f_fold on Rev, Map, RangeInclusive, etc.

open Core_models
open Core_models.Iter.Traits.Iterator
open Core_models.Iter.Bundle

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_rev (v_I: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_map (v_I: Type0) (v_F: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IteratorMethods v_I)
  : t_IteratorMethods (t_Map v_I v_F)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_range_inclusive (v_T: Type0)
  : t_IteratorMethods (Core_models.Ops.Range.t_RangeInclusive v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_iterator_methods_slice_iter (v_T: Type0)
  : t_IteratorMethods (Core_models.Slice.Iter.t_Iter v_T)

/// IntoIterator instances
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_rev (v_I: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator
      (Core_models.Iter.Adapters.Rev.t_Rev v_I)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_map (v_I: Type0) (v_F: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Map v_I v_F)

/// IntoIterator for Vec -- placed here instead of Iterator.fst to avoid
/// circular dependency (Iterator -> Alloc.Vec -> Iterator).
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_into_iter_vec (#v_T: Type0) (#v_A: Type0)
  : Core_models.Iter.Traits.Collect.t_IntoIterator (Alloc.Vec.t_Vec v_T v_A)
