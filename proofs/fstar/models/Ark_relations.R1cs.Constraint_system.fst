module Ark_relations.R1cs.Constraint_system

open Rust_primitives

(* Types - ordered so all types are defined before values *)
assume new type t_ConstraintSystemRef (f : Type0) : Type0
assume new type t_ConstraintSystem (f : Type0) : Type0
assume new type t_ConstraintSynthesizer (c : Type0) (f : Type0) : Type0

noeq type t_ConstraintMatrices (f : Type0) = {
  f_a : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & f) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
  f_b : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & f) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
  f_c : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & f) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
  f_num_instance_variables : usize;
  f_num_witness_variables : usize;
  f_num_constraints : usize;
}

type t_SynthesisMode_Prove_record = { f_construct_matrices : bool }
type t_SynthesisMode =
  | SynthesisMode_Prove : t_SynthesisMode_Prove_record -> t_SynthesisMode
  | SynthesisMode_Setup : t_SynthesisMode

(* Operations *)
assume val impl_1__new_ref : #f:Type0 -> unit -> t_ConstraintSystemRef f
assume val impl_7__set_mode : #f:Type0 -> t_ConstraintSystemRef f -> t_SynthesisMode -> Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError
assume val impl_7__finalize : #f:Type0 -> t_ConstraintSystemRef f -> unit
assume val impl_7__num_instance_variables : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__num_witness_variables : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__num_constraints : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__to_matrices : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Result.t_Result (t_ConstraintMatrices f) Ark_relations.R1cs.Error.t_SynthesisError
assume val impl_7__is_satisfied : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Result.t_Result bool Ark_relations.R1cs.Error.t_SynthesisError
assume val impl_7__borrow : #f:Type0 -> t_ConstraintSystemRef f -> t_ConstraintSystem f
assume val f_generate_constraints : #f:Type0 -> #c:Type0 -> c -> t_ConstraintSystemRef f -> Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError
