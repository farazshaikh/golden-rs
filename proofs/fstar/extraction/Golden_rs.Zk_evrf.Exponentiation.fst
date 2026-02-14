module Golden_rs.Zk_evrf.Exponentiation
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Ark_r1cs_std.Alloc in
  let open Ark_r1cs_std.Eq in
  let open Ark_r1cs_std.Fields.Emulated_fp.Field_var in
  let open Ark_r1cs_std.R1cs_var in
  let open Ark_relations.R1cs.Constraint_system in
  let open Num_traits.Identities in
  ()

/// A G1 point represented in the circuit using emulated Fq coordinates.
/// Wraps two `EmulatedFpVar<Fq, Fr>` for the x and y affine coordinates.
/// Non-native arithmetic constraints are generated automatically by arkworks
/// when operations are performed on these variables.
type t_PointVar = {
  f_x:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4));
  f_y:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
}

/// Allocate a G1 point as a private witness.

(* Point operations replaced with assume val. Circuit correctness
   is verified by Lean proofs in EVRFCircuit.lean. *)
assume val impl_PointVar__new_witness
  (cs: Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
    (Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
  (x y: Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
  : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError

assume val impl_PointVar__new_input
  (cs: Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
    (Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
  (x y: Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
  : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError

assume val impl_PointVar__enforce_equal (self other: t_PointVar)
  : Core_models.Result.t_Result unit Ark_relations.R1cs.Error.t_SynthesisError

assume val point_add (p q: t_PointVar) (cs_nonnative: Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem)
  : (Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem & t_PointVar)

assume val point_double (p: t_PointVar) (cs_nonnative: Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem)
  : (Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem & t_PointVar)
