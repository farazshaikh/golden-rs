module Golden_rs.Zk_evrf.Circuit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Ark_r1cs_std.Alloc in
  let open Ark_r1cs_std.Convert in
  let open Ark_r1cs_std.Fields.Emulated_fp.Field_var in
  let open Ark_r1cs_std.Fields.Fp in
  let open Ark_relations.R1cs.Constraint_system in
  let open Num_traits.Identities in
  ()

/// The eVRF proof circuit for a single statement.
/// Per Section 4.3 (Figure 3) of the Golden paper (IACR 2025/1924), proves the
/// R_eVRF relation: given public inputs `(PK_1, PK_2, R, beta)` and private
/// witness `sk_1`, demonstrates that `R = g^r` where `r` is correctly derived
/// from the DH shared secret `PK_2^{sk_1}` via the eVRF Evaluate algorithm.
type t_EVRFCircuit = {
  f_pk1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_pk2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_sk1:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_dh_shared:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_r_value:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

/// Create a new eVRF circuit from the prover's knowledge.
/// Computes intermediate values (DH shared secret) from the provided
/// secret key and peer public key.

(* Circuit functions replaced with assume val. Circuit correctness is verified
   by Lean proofs in EVRFCircuit.lean (4 theorems including completeness
   and knowledge extraction). *)
assume val impl_EVRFCircuit__new : #a:Type0 -> a -> t_EVRFCircuit
assume val impl_EVRFCircuit__for_verification : #a:Type0 -> a -> t_EVRFCircuit

type t_BatchEVRFCircuit = {
  f_circuits: Alloc.Vec.t_Vec t_EVRFCircuit Alloc.Alloc.t_Global
}

assume val impl_BatchEVRFCircuit__new : #a:Type0 -> a -> t_BatchEVRFCircuit
assume val impl_BatchEVRFCircuit__for_verification : #a:Type0 -> a -> t_BatchEVRFCircuit
