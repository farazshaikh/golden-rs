module Ark_r1cs_std.R1cs_var

/// R1CSVar trait
class t_R1CSVar (v_Self: Type0) (v_F: Type0) = { __rv_dummy : unit; }
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_r1cs_var_blanket (#v_S #v_F: Type0) : t_R1CSVar v_S v_F

/// f_value: hax calls #VarType #FieldType #solve var
/// For EmulatedFpVar<TargetField, ConstraintField>, f_value returns TargetField.
/// Using an extra implicit v_Val for the return type (inferred from let-binding context).
assume val f_value : #v_V:Type0 -> #v_F:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_R1CSVar v_V v_F
  -> #v_Val:Type0
  -> v_V -> Core_models.Result.t_Result v_Val Ark_relations.R1cs.Error.t_SynthesisError
