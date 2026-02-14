module Libspartan

open Rust_primitives

assume new type t_Instance (f : Type0) : Type0
assume new type t_Assignment (f : Type0) : Type0
assume new type t_SNARK (f : Type0) : Type0
assume new type t_NIZK (f : Type0) : Type0
assume new type t_NIZKGens (f : Type0) : Type0

/// Instance::new(num_cons, num_witness, num_inputs, a_triples, b_triples, c_triples)
/// Returns Result<Instance, R1CSError>
assume val impl_1__new : #f:Type0 -> usize -> usize -> usize
  -> t_Slice (usize & usize & f) -> t_Slice (usize & usize & f) -> t_Slice (usize & usize & f)
  -> Core_models.Result.t_Result (t_Instance f) Libspartan.Errors.t_R1CSError

/// Assignment::new(values) -- takes a single Slice, returns Result
assume val impl__new : #f:Type0 -> t_Slice f
  -> Core_models.Result.t_Result (t_Assignment f) Libspartan.Errors.t_R1CSError

/// SNARK::prove/verify
assume val impl_SNARK__prove : #f:Type0 -> #v_A:Type0 -> #v_B:Type0 -> #v_C:Type0 -> #v_D:Type0
  -> v_A -> v_B -> v_C -> v_D
  -> Core_models.Result.t_Result (t_SNARK f) Libspartan.Errors.t_ProofVerifyError

assume val impl_SNARK__verify : #f:Type0 -> #v_A:Type0 -> #v_B:Type0 -> #v_C:Type0 -> #v_D:Type0
  -> v_A -> v_B -> v_C -> v_D
  -> Core_models.Result.t_Result bool Libspartan.Errors.t_ProofVerifyError

/// NIZKGens::new(num_cons, num_vars, num_inputs)
assume val impl_4__new : #f:Type0 -> usize -> usize -> usize -> t_NIZKGens f

/// NIZK::prove returns (updated_transcript, proof)
assume val impl_5__prove : #f:Type0
  -> #v_Instance:Type0 -> #v_Vars:Type0 -> #v_Inputs:Type0 -> #v_Gens:Type0 -> #v_Transcript:Type0
  -> v_Instance -> v_Vars -> v_Inputs -> v_Gens -> v_Transcript
  -> (v_Transcript & t_NIZK f)

/// NIZK::verify(proof, instance, inputs, transcript, gens) -> (transcript, Result)
assume val impl_5__verify : #f:Type0
  -> #v_A:Type0 -> #v_B:Type0 -> #v_C:Type0 -> #v_D:Type0 -> #v_E:Type0
  -> v_A -> v_B -> v_C -> v_D -> v_E
  -> (v_D & Core_models.Result.t_Result Prims.unit Libspartan.Errors.t_ProofVerifyError)
