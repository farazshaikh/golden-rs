module Ark_r1cs_std.Eq

/// EqGadget trait
class t_EqGadget (v_Self: Type0) (v_F: Type0) = { __eq_dummy : unit; }
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_eq_gadget_blanket (#v_S #v_F: Type0) : t_EqGadget v_S v_F

/// f_enforce_equal: hax calls #VarType #FieldType #solve a b
assume val f_enforce_equal : #v_V:Type0 -> #v_F:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_EqGadget v_V v_F
  -> v_V -> v_V -> Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError
