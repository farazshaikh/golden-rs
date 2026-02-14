module Ark_r1cs_std.Alloc

open Rust_primitives
assume val f_new_input : #f:Type0 -> #v:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> unit -> Core_models.Result.t_Result v Ark_relations.R1cs.Error.t_SynthesisError
assume val f_new_witness : #f:Type0 -> #v:Type0 -> Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef f -> unit -> Core_models.Result.t_Result v Ark_relations.R1cs.Error.t_SynthesisError
