module Ark_r1cs_std.Convert

open Rust_primitives
/// ToBitsGadget trait
class t_ToBitsLE (v_Self: Type0) (v_F: Type0) = { __tbl_dummy : unit; }
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_to_bits_le_blanket (#v_S #v_F: Type0) : t_ToBitsLE v_S v_F

/// f_to_bits_le: hax calls #VarType #FieldType #solve var
assume val f_to_bits_le : #v_V:Type0 -> #v_F:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_ToBitsLE v_V v_F
  -> v_V -> Core_models.Result.t_Result (Alloc.Vec.t_Vec (Ark_r1cs_std.Boolean.t_Boolean v_F) Alloc.Alloc.t_Global) Ark_relations.R1cs.Error.t_SynthesisError
