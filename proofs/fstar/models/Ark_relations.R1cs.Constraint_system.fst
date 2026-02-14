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
