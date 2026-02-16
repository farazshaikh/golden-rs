module Ark_r1cs_std.Alloc

open Rust_primitives

/// AllocVar trait (for tcresolve)
class t_AllocVar (v_Self: Type0) (v_F: Type0) = { __av_dummy : unit; }
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_alloc_var_blanket (#v_S #v_F: Type0) : t_AllocVar v_S v_F

/// f_new_input/f_new_witness: hax calls with 7 implicits + 2 explicit
/// Pattern: #VarType #TargetField #ConstraintField #solve #ExtraType #CSRefType #ClosureType cs_ref closure
assume val f_new_input : #v_V:Type0 -> #v_T:Type0 -> #v_F:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_AllocVar v_V v_F
  -> #v_T2:Type0 -> #v_CS:Type0 -> #v_Closure:Type0
  -> v_CS -> v_Closure
  -> Core_models.Result.t_Result v_V Ark_relations.R1cs.Error.t_SynthesisError

assume val f_new_witness : #v_V:Type0 -> #v_T:Type0 -> #v_F:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_AllocVar v_V v_F
  -> #v_T2:Type0 -> #v_CS:Type0 -> #v_Closure:Type0
  -> v_CS -> v_Closure
  -> Core_models.Result.t_Result v_V Ark_relations.R1cs.Error.t_SynthesisError
