module Ark_relations.R1cs.Constraint_system

assume new type t_ConstraintMatrices (f : Type0) : Type0
assume new type t_ConstraintSystemRef (f : Type0) : Type0

assume new type t_ConstraintSynthesizer (f : Type0) : Type0

open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend
assume val impl_1__new_ref : #f:Type0 -> unit -> t_ConstraintSystemRef f

assume val impl_7__set_mode : #f:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> unit -> unit



type t_SynthesisMode =
  | SynthesisMode_Prove : t_SynthesisMode
  | SynthesisMode_Setup : t_SynthesisMode

assume val f_generate_constraints : #f:Type0 -> #c:Type0 -> c -> t_ConstraintSystemRef f -> Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError

assume val impl_7__finalize : #f:Type0 -> t_ConstraintSystemRef f -> unit

assume val impl_7__is_satisfied : #f:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> Core_models.Result.t_Result bool Ark_relations.R1cs.Error.t_SynthesisError

assume val impl_7__num_instance_variables : #f:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> Rust_primitives.Integers.usize
assume val impl_7__num_witness_variables : #f:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> Rust_primitives.Integers.usize
assume val impl_7__num_constraints : #f:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> Rust_primitives.Integers.usize

assume val impl_7__to_matrices : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Result.t_Result (t_ConstraintMatrices f) Ark_relations.R1cs.Error.t_SynthesisError
