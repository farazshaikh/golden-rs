module Ark_r1cs_std.Fields.Emulated_fp.Field_var

assume new type t_EmulatedFpVar (target : Type0) (base : Type0) : Type0

/// Arithmetic instances for EmulatedFpVar
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_emulated_add (t b : Type0) :
  Core_models.Ops.Arith.t_Add (t_EmulatedFpVar t b) (t_EmulatedFpVar t b)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_emulated_sub (t b : Type0) :
  Core_models.Ops.Arith.t_Sub (t_EmulatedFpVar t b) (t_EmulatedFpVar t b)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_emulated_mul (t b : Type0) :
  Core_models.Ops.Arith.t_Mul (t_EmulatedFpVar t b) (t_EmulatedFpVar t b)
