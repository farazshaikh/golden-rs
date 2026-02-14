module Ark_r1cs_std.Fields.Fp

assume new type t_FpVar (f : Type0) : Type0

/// Arithmetic instances for FpVar
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fpvar_mul (f : Type0) :
  Core_models.Ops.Arith.t_Mul (t_FpVar f) (t_FpVar f)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fpvar_add (f : Type0) :
  Core_models.Ops.Arith.t_Add (t_FpVar f) (t_FpVar f)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fpvar_sub (f : Type0) :
  Core_models.Ops.Arith.t_Sub (t_FpVar f) (t_FpVar f)
