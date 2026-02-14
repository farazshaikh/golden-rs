module Ark_relations.R1cs.Constraint_system

open Rust_primitives

(* Types - ordered so all types are defined before values *)
assume new type t_ConstraintSystemRef (f : Type0) : Type0
/// ConstraintSystem is a record with assignment vectors accessible via field access.
noeq type t_ConstraintSystem (f : Type0) = {
  f_instance_assignment : Alloc.Vec.t_Vec f Alloc.Alloc.t_Global;
  f_witness_assignment : Alloc.Vec.t_Vec f Alloc.Alloc.t_Global;
}
/// ConstraintSynthesizer as a typeclass -- the extraction creates concrete instances
/// with f_generate_constraints_pre/post/f_generate_constraints fields.
class t_ConstraintSynthesizer (v_C : Type0) (v_F : Type0) = {
  f_generate_constraints_pre : v_C -> t_ConstraintSystemRef v_F -> Type0;
  f_generate_constraints_post : v_C -> t_ConstraintSystemRef v_F -> Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError -> Type0;
  f_generate_constraints : x0:v_C -> x1:t_ConstraintSystemRef v_F
    -> Prims.Pure (Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError)
        (f_generate_constraints_pre x0 x1)
        (fun result -> f_generate_constraints_post x0 x1 result);
}

noeq type t_ConstraintMatrices (f : Type0) = {
  f_a : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & usize) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
  f_b : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & usize) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
  f_c : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec (f & usize) Alloc.Alloc.t_Global) Alloc.Alloc.t_Global;
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
assume val impl_7__set_mode : #f:Type0 -> t_ConstraintSystemRef f -> t_SynthesisMode -> unit
assume val impl_7__finalize : #f:Type0 -> t_ConstraintSystemRef f -> unit
assume val impl_7__num_instance_variables : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__num_witness_variables : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__num_constraints : #f:Type0 -> t_ConstraintSystemRef f -> usize
assume val impl_7__to_matrices : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Option.t_Option (t_ConstraintMatrices f)
assume val impl_7__is_satisfied : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Result.t_Result bool Ark_relations.R1cs.Error.t_SynthesisError
assume val impl_7__borrow : #f:Type0 -> t_ConstraintSystemRef f -> Core_models.Option.t_Option (Core_models.Cell.t_Ref (t_ConstraintSystem f))

/// Standalone f_generate_constraints accessor (delegates to typeclass method).
/// The typeclass method is defined in the t_ConstraintSynthesizer class above.
/// hax calls: f_generate_constraints #CircuitType #FieldType #solve circuit cs
/// The #solve fills the tcresolve for the t_ConstraintSynthesizer instance.
