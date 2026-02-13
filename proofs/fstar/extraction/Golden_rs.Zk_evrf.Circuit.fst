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
let impl_EVRFCircuit__new
      (sk1:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (pk1 pk2: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (r_value:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (r_commitment:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_EVRFCircuit =
  let dh_shared:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          pk2
          sk1
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  {
    f_pk1 = pk1;
    f_pk2 = pk2;
    f_r_commitment = r_commitment;
    f_beta = beta;
    f_sk1 = sk1;
    f_dh_shared = dh_shared;
    f_r_value = r_value
  }
  <:
  t_EVRFCircuit

/// Create a circuit for verification mode (no private witness).
/// Uses zero values for private witnesses -- only the constraint structure matters.
/// The verifier needs this to reconstruct the same R1CS matrices as the prover.
let impl_EVRFCircuit__for_verification
      (pk1 pk2 r_commitment:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_EVRFCircuit =
  {
    f_pk1 = pk1;
    f_pk2 = pk2;
    f_r_commitment = r_commitment;
    f_beta = beta;
    f_sk1
    =
    Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      ();
    f_dh_shared
    =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ();
    f_r_value
    =
    Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      ()
  }
  <:
  t_EVRFCircuit

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Ark_relations.R1cs.Constraint_system.t_ConstraintSynthesizer t_EVRFCircuit
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
  {
    f_generate_constraints_pre
    =
    (fun
        (self: t_EVRFCircuit)
        (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        ->
        true);
    f_generate_constraints_post
    =
    (fun
        (self: t_EVRFCircuit)
        (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (out: Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
        ->
        true);
    f_generate_constraints
    =
    fun
      (self: t_EVRFCircuit)
      (cs:
        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      ->
      let pk1_x:Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
        if self.f_pk1.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
        then
          Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
        else self.f_pk1.Ark_ec.Models.Short_weierstrass.Affine.f_x
      in
      let pk1_y:Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
        if self.f_pk1.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
        then
          Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
        else self.f_pk1.Ark_ec.Models.Short_weierstrass.Affine.f_y
      in
      match
        Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #(Prims.unit
              -> Core_models.Result.t_Result
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  Ark_relations.R1cs.Error.t_SynthesisError)
          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #FStar.Tactics.Typeclasses.solve
              cs
            <:
            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok pk1_x
              <:
              Core_models.Result.t_Result
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                Ark_relations.R1cs.Error.t_SynthesisError)
        <:
        Core_models.Result.t_Result
          (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          Ark_relations.R1cs.Error.t_SynthesisError
      with
      | Core_models.Result.Result_Ok e_pk1_x_var ->
        (match
            Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #(Prims.unit
                  -> Core_models.Result.t_Result
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      Ark_relations.R1cs.Error.t_SynthesisError)
              (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #FStar.Tactics.Typeclasses.solve
                  cs
                <:
                Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              (fun temp_0_ ->
                  let _:Prims.unit = temp_0_ in
                  Core_models.Result.Result_Ok pk1_y
                  <:
                  Core_models.Result.t_Result
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    Ark_relations.R1cs.Error.t_SynthesisError)
            <:
            Core_models.Result.t_Result
              (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              Ark_relations.R1cs.Error.t_SynthesisError
          with
          | Core_models.Result.Result_Ok e_pk1_y_var ->
            let pk2_x:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
              if self.f_pk2.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
              then
                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  ()
              else self.f_pk2.Ark_ec.Models.Short_weierstrass.Affine.f_x
            in
            let pk2_y:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
              if self.f_pk2.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
              then
                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  ()
              else self.f_pk2.Ark_ec.Models.Short_weierstrass.Affine.f_y
            in
            (match
                Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Prims.unit
                      -> Core_models.Result.t_Result
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          Ark_relations.R1cs.Error.t_SynthesisError)
                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #FStar.Tactics.Typeclasses.solve
                      cs
                    <:
                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      Core_models.Result.Result_Ok pk2_x
                      <:
                      Core_models.Result.t_Result
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        Ark_relations.R1cs.Error.t_SynthesisError)
                <:
                Core_models.Result.t_Result
                  (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  Ark_relations.R1cs.Error.t_SynthesisError
              with
              | Core_models.Result.Result_Ok e_pk2_x_var ->
                (match
                    Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Prims.unit
                          -> Core_models.Result.t_Result
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              ) Ark_relations.R1cs.Error.t_SynthesisError)
                      (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          #FStar.Tactics.Typeclasses.solve
                          cs
                        <:
                        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (fun temp_0_ ->
                          let _:Prims.unit = temp_0_ in
                          Core_models.Result.Result_Ok pk2_y
                          <:
                          Core_models.Result.t_Result
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                            Ark_relations.R1cs.Error.t_SynthesisError)
                    <:
                    Core_models.Result.t_Result
                      (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      Ark_relations.R1cs.Error.t_SynthesisError
                  with
                  | Core_models.Result.Result_Ok e_pk2_y_var ->
                    let r_x:Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
                      if self.f_r_commitment.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                      then
                        Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          #FStar.Tactics.Typeclasses.solve
                          ()
                      else self.f_r_commitment.Ark_ec.Models.Short_weierstrass.Affine.f_x
                    in
                    let r_y:Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
                      if self.f_r_commitment.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                      then
                        Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          #FStar.Tactics.Typeclasses.solve
                          ()
                      else self.f_r_commitment.Ark_ec.Models.Short_weierstrass.Affine.f_y
                    in
                    (match
                        Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              )
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              ))
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                          #FStar.Tactics.Typeclasses.solve
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          #(Prims.unit
                              -> Core_models.Result.t_Result
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                      (mk_usize 6)) Ark_relations.R1cs.Error.t_SynthesisError)
                          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)))
                              #FStar.Tactics.Typeclasses.solve
                              cs
                            <:
                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          (fun temp_0_ ->
                              let _:Prims.unit = temp_0_ in
                              Core_models.Result.Result_Ok r_x
                              <:
                              Core_models.Result.t_Result
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                    (mk_usize 6)) Ark_relations.R1cs.Error.t_SynthesisError)
                        <:
                        Core_models.Result.t_Result
                          (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              )
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              )) Ark_relations.R1cs.Error.t_SynthesisError
                      with
                      | Core_models.Result.Result_Ok e_r_x_var ->
                        (match
                            Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                      (mk_usize 6))
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4)))
                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              )
                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              )
                              #FStar.Tactics.Typeclasses.solve
                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              )
                              #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)))
                              #(Prims.unit
                                  -> Core_models.Result.t_Result
                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                          (mk_usize 6)) Ark_relations.R1cs.Error.t_SynthesisError)
                              (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                  #FStar.Tactics.Typeclasses.solve
                                  cs
                                <:
                                Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)))
                              (fun temp_0_ ->
                                  let _:Prims.unit = temp_0_ in
                                  Core_models.Result.Result_Ok r_y
                                  <:
                                  Core_models.Result.t_Result
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                        (mk_usize 6)) Ark_relations.R1cs.Error.t_SynthesisError)
                            <:
                            Core_models.Result.t_Result
                              (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                      (mk_usize 6))
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))) Ark_relations.R1cs.Error.t_SynthesisError
                          with
                          | Core_models.Result.Result_Ok e_r_y_var ->
                            (match
                                Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                                  #FStar.Tactics.Typeclasses.solve
                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                  #(Prims.unit
                                      -> Core_models.Result.t_Result
                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      #FStar.Tactics.Typeclasses.solve
                                      cs
                                    <:
                                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                  (fun temp_0_ ->
                                      let _:Prims.unit = temp_0_ in
                                      Core_models.Result.Result_Ok self.f_beta
                                      <:
                                      Core_models.Result.t_Result
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)) Ark_relations.R1cs.Error.t_SynthesisError)
                                <:
                                Core_models.Result.t_Result
                                  (Ark_r1cs_std.Fields.Fp.t_FpVar
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))) Ark_relations.R1cs.Error.t_SynthesisError
                              with
                              | Core_models.Result.Result_Ok e_beta_var ->
                                (match
                                    Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #FStar.Tactics.Typeclasses.solve
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      #(Prims.unit
                                          -> Core_models.Result.t_Result
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                              Ark_relations.R1cs.Error.t_SynthesisError)
                                      (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          #FStar.Tactics.Typeclasses.solve
                                          cs
                                        <:
                                        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      (fun temp_0_ ->
                                          let _:Prims.unit = temp_0_ in
                                          Core_models.Result.Result_Ok self.f_sk1
                                          <:
                                          Core_models.Result.t_Result
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4))
                                            Ark_relations.R1cs.Error.t_SynthesisError)
                                    <:
                                    Core_models.Result.t_Result
                                      (Ark_r1cs_std.Fields.Fp.t_FpVar
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4))) Ark_relations.R1cs.Error.t_SynthesisError
                                  with
                                  | Core_models.Result.Result_Ok sk1_var ->
                                    (match
                                        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          #FStar.Tactics.Typeclasses.solve
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          #(Prims.unit
                                              -> Core_models.Result.t_Result
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4))
                                                  Ark_relations.R1cs.Error.t_SynthesisError)
                                          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                              #FStar.Tactics.Typeclasses.solve
                                              cs
                                            <:
                                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          (fun temp_0_ ->
                                              let _:Prims.unit = temp_0_ in
                                              Core_models.Result.Result_Ok self.f_r_value
                                              <:
                                              Core_models.Result.t_Result
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4))
                                                Ark_relations.R1cs.Error.t_SynthesisError)
                                        <:
                                        Core_models.Result.t_Result
                                          (Ark_r1cs_std.Fields.Fp.t_FpVar
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          Ark_relations.R1cs.Error.t_SynthesisError
                                      with
                                      | Core_models.Result.Result_Ok r_var ->
                                        let dh_x:Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                          (mk_usize 6) =
                                          if
                                            self.f_dh_shared
                                              .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                          then
                                            Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              #FStar.Tactics.Typeclasses.solve
                                              ()
                                          else
                                            self.f_dh_shared
                                              .Ark_ec.Models.Short_weierstrass.Affine.f_x
                                        in
                                        let dh_y:Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                          (mk_usize 6) =
                                          if
                                            self.f_dh_shared
                                              .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                          then
                                            Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              #FStar.Tactics.Typeclasses.solve
                                              ()
                                          else
                                            self.f_dh_shared
                                              .Ark_ec.Models.Short_weierstrass.Affine.f_y
                                        in
                                        (match
                                            Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4)))
                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                              #FStar.Tactics.Typeclasses.solve
                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                              #(Prims.unit
                                                  -> Core_models.Result.t_Result
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      Ark_relations.R1cs.Error.t_SynthesisError)
                                              (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  cs
                                                <:
                                                Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                              (fun temp_0_ ->
                                                  let _:Prims.unit = temp_0_ in
                                                  Core_models.Result.Result_Ok dh_x
                                                  <:
                                                  Core_models.Result.t_Result
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                            (mk_usize 6)) (mk_usize 6))
                                                    Ark_relations.R1cs.Error.t_SynthesisError)
                                            <:
                                            Core_models.Result.t_Result
                                              (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4)))
                                              Ark_relations.R1cs.Error.t_SynthesisError
                                          with
                                          | Core_models.Result.Result_Ok e_dh_x_var ->
                                            (match
                                                Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4)))
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)))
                                                  #(Prims.unit
                                                      -> Core_models.Result.t_Result
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                  (mk_usize 6)) (mk_usize 6))
                                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                (mk_usize 4)) (mk_usize 4)))
                                                      #FStar.Tactics.Typeclasses.solve
                                                      cs
                                                    <:
                                                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)))
                                                  (fun temp_0_ ->
                                                      let _:Prims.unit = temp_0_ in
                                                      Core_models.Result.Result_Ok dh_y
                                                      <:
                                                      Core_models.Result.t_Result
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                (mk_usize 6)) (mk_usize 6))
                                                        Ark_relations.R1cs.Error.t_SynthesisError)
                                                <:
                                                Core_models.Result.t_Result
                                                  (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4)))
                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                              with
                                              | Core_models.Result.Result_Ok e_dh_y_var ->
                                                (match
                                                    Ark_r1cs_std.Convert.f_to_bits_le #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                (mk_usize 4)) (mk_usize 4)))
                                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4))
                                                      #FStar.Tactics.Typeclasses.solve
                                                      sk1_var
                                                    <:
                                                    Core_models.Result.t_Result
                                                      (Alloc.Vec.t_Vec
                                                          (Ark_r1cs_std.Boolean.t_Boolean
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          Alloc.Alloc.t_Global)
                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                  with
                                                  | Core_models.Result.Result_Ok sk1_bits ->
                                                    let _:Prims.unit =
                                                      Hax_lib.v_assert ((Alloc.Vec.impl_1__len #(Ark_r1cs_std.Boolean.t_Boolean
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4)))
                                                              #Alloc.Alloc.t_Global
                                                              sk1_bits
                                                            <:
                                                            usize) >=.
                                                          mk_usize 255
                                                          <:
                                                          bool)
                                                    in
                                                    let _:Ark_r1cs_std.Fields.Fp.t_FpVar
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)) =
                                                      Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4)))
                                                        #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4)))
                                                        #FStar.Tactics.Typeclasses.solve
                                                        sk1_var
                                                        r_var
                                                    in
                                                    Core_models.Result.Result_Ok (() <: Prims.unit)
                                                    <:
                                                    Core_models.Result.t_Result Prims.unit
                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                  | Core_models.Result.Result_Err err ->
                                                    Core_models.Result.Result_Err err
                                                    <:
                                                    Core_models.Result.t_Result Prims.unit
                                                      Ark_relations.R1cs.Error.t_SynthesisError)
                                              | Core_models.Result.Result_Err err ->
                                                Core_models.Result.Result_Err err
                                                <:
                                                Core_models.Result.t_Result Prims.unit
                                                  Ark_relations.R1cs.Error.t_SynthesisError)
                                          | Core_models.Result.Result_Err err ->
                                            Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result Prims.unit
                                              Ark_relations.R1cs.Error.t_SynthesisError)
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit
                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit
                                      Ark_relations.R1cs.Error.t_SynthesisError)
                              | Core_models.Result.Result_Err err ->
                                Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit
                                  Ark_relations.R1cs.Error.t_SynthesisError)
                          | Core_models.Result.Result_Err err ->
                            Core_models.Result.Result_Err err
                            <:
                            Core_models.Result.t_Result Prims.unit
                              Ark_relations.R1cs.Error.t_SynthesisError)
                      | Core_models.Result.Result_Err err ->
                        Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result Prims.unit
                          Ark_relations.R1cs.Error.t_SynthesisError)
                  | Core_models.Result.Result_Err err ->
                    Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
                )
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
  }

/// Batched eVRF circuit: proves `n-1` eVRF evaluations with shared `sk_1`.
/// Per Section 5.3 of the Golden paper (IACR 2025/1924): the `sk_1`
/// bit-decomposition and `g^{sk_1}` exponentiation are computed once and
/// reused for all `n-1` peer evaluations. This reduces the total constraint
/// count compared to `n-1` separate proofs (~29% reduction per Section 4.6).
type t_BatchEVRFCircuit = {
  f_sk1:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_my_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_peers:Alloc.Vec.t_Vec
    (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global;
  f_pads:Alloc.Vec.t_Vec
    (u32 &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

/// Create a new batched eVRF circuit.
let impl_BatchEVRFCircuit__new
      (sk1:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (my_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (peers:
          t_Slice
          (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (pads:
          t_Slice
          (u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_BatchEVRFCircuit =
  {
    f_sk1 = sk1;
    f_my_pk = my_pk;
    f_peers
    =
    Alloc.Slice.impl__to_vec #(u32 &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      peers;
    f_pads
    =
    Alloc.Slice.impl__to_vec #(u32 &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      pads;
    f_beta = beta
  }
  <:
  t_BatchEVRFCircuit

/// Create a batch circuit for verification mode.
/// Uses zero values for private witnesses.
let impl_BatchEVRFCircuit__for_verification
      (my_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (peers pad_commitments:
          t_Slice
          (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_BatchEVRFCircuit =
  let
  (pads:
    Alloc.Vec.t_Vec
      (u32 &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    (u32 &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec
          (u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          #FStar.Tactics.Typeclasses.solve
          #(u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(
                (u32 &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          )
          (Core_models.Slice.impl__iter #(u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              pad_commitments
            <:
            Core_models.Slice.Iter.t_Iter
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          (fun temp_0_ ->
              let
              (id: u32),
              (rc:
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
                temp_0_
              in
              id,
              (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  ()
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
              rc
              <:
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
  in
  {
    f_sk1
    =
    Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      ();
    f_my_pk = my_pk;
    f_peers
    =
    Alloc.Slice.impl__to_vec #(u32 &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      peers;
    f_pads = pads;
    f_beta = beta
  }
  <:
  t_BatchEVRFCircuit

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Ark_relations.R1cs.Constraint_system.t_ConstraintSynthesizer t_BatchEVRFCircuit
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
  {
    f_generate_constraints_pre
    =
    (fun
        (self: t_BatchEVRFCircuit)
        (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        ->
        true);
    f_generate_constraints_post
    =
    (fun
        (self: t_BatchEVRFCircuit)
        (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (out1: Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
        ->
        true);
    f_generate_constraints
    =
    fun
      (self: t_BatchEVRFCircuit)
      (cs:
        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      ->
      match
        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Fp.t_FpVar
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #(Prims.unit
              -> Core_models.Result.t_Result
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Ark_relations.R1cs.Error.t_SynthesisError)
          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #FStar.Tactics.Typeclasses.solve
              cs
            <:
            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok self.f_sk1
              <:
              Core_models.Result.t_Result
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                Ark_relations.R1cs.Error.t_SynthesisError)
        <:
        Core_models.Result.t_Result
          (Ark_r1cs_std.Fields.Fp.t_FpVar
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          Ark_relations.R1cs.Error.t_SynthesisError
      with
      | Core_models.Result.Result_Ok sk1_var ->
        (match
            Ark_r1cs_std.Convert.f_to_bits_le #(Ark_r1cs_std.Fields.Fp.t_FpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              sk1_var
            <:
            Core_models.Result.t_Result
              (Alloc.Vec.t_Vec
                  (Ark_r1cs_std.Boolean.t_Boolean
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  Alloc.Alloc.t_Global) Ark_relations.R1cs.Error.t_SynthesisError
          with
          | Core_models.Result.Result_Ok e_sk1_bits ->
            let pk1_x:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
              if self.f_my_pk.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
              then
                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  ()
              else self.f_my_pk.Ark_ec.Models.Short_weierstrass.Affine.f_x
            in
            let pk1_y:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) =
              if self.f_my_pk.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
              then
                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  ()
              else self.f_my_pk.Ark_ec.Models.Short_weierstrass.Affine.f_y
            in
            (match
                Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Prims.unit
                      -> Core_models.Result.t_Result
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          Ark_relations.R1cs.Error.t_SynthesisError)
                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #FStar.Tactics.Typeclasses.solve
                      cs
                    <:
                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      Core_models.Result.Result_Ok pk1_x
                      <:
                      Core_models.Result.t_Result
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        Ark_relations.R1cs.Error.t_SynthesisError)
                <:
                Core_models.Result.t_Result
                  (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  Ark_relations.R1cs.Error.t_SynthesisError
              with
              | Core_models.Result.Result_Ok e_pk1_x_var ->
                (match
                    Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Prims.unit
                          -> Core_models.Result.t_Result
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)
                              ) Ark_relations.R1cs.Error.t_SynthesisError)
                      (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          #FStar.Tactics.Typeclasses.solve
                          cs
                        <:
                        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (fun temp_0_ ->
                          let _:Prims.unit = temp_0_ in
                          Core_models.Result.Result_Ok pk1_y
                          <:
                          Core_models.Result.t_Result
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                            Ark_relations.R1cs.Error.t_SynthesisError)
                    <:
                    Core_models.Result.t_Result
                      (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      Ark_relations.R1cs.Error.t_SynthesisError
                  with
                  | Core_models.Result.Result_Ok e_pk1_y_var ->
                    (match
                        Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Fp.t_FpVar
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                          #FStar.Tactics.Typeclasses.solve
                          #(Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          #(Prims.unit
                              -> Core_models.Result.t_Result
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4)) Ark_relations.R1cs.Error.t_SynthesisError)
                          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)))
                              #FStar.Tactics.Typeclasses.solve
                              cs
                            <:
                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          (fun temp_0_ ->
                              let _:Prims.unit = temp_0_ in
                              Core_models.Result.Result_Ok self.f_beta
                              <:
                              Core_models.Result.t_Result
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)) Ark_relations.R1cs.Error.t_SynthesisError)
                        <:
                        Core_models.Result.t_Result
                          (Ark_r1cs_std.Fields.Fp.t_FpVar
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          Ark_relations.R1cs.Error.t_SynthesisError
                      with
                      | Core_models.Result.Result_Ok e_beta_var ->
                        (match
                            Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                                  #(Alloc.Vec.t_Vec
                                      (u32 &
                                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                        Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                                  #FStar.Tactics.Typeclasses.solve
                                  self.f_peers
                                <:
                                Core_models.Slice.Iter.t_Iter
                                (u32 &
                                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config))
                              ()
                              (fun temp_0_ temp_1_ ->
                                  let _:Prims.unit = temp_0_ in
                                  let
                                  (peer_id: u32),
                                  (peer_pk:
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config) =
                                    temp_1_
                                  in
                                  let pk2_x:Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                    (mk_usize 6) =
                                    if peer_pk.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                    then
                                      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                            (mk_usize 6))
                                        #FStar.Tactics.Typeclasses.solve
                                        ()
                                    else peer_pk.Ark_ec.Models.Short_weierstrass.Affine.f_x
                                  in
                                  let pk2_y:Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                    (mk_usize 6) =
                                    if peer_pk.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                    then
                                      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                            (mk_usize 6))
                                        #FStar.Tactics.Typeclasses.solve
                                        ()
                                    else peer_pk.Ark_ec.Models.Short_weierstrass.Affine.f_y
                                  in
                                  match
                                    Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6))
                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4)))
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                          (mk_usize 6))
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #FStar.Tactics.Typeclasses.solve
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                          (mk_usize 6))
                                      #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      #(Prims.unit
                                          -> Core_models.Result.t_Result
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              Ark_relations.R1cs.Error.t_SynthesisError)
                                      (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          #FStar.Tactics.Typeclasses.solve
                                          cs
                                        <:
                                        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4)))
                                      (fun temp_0_ ->
                                          let _:Prims.unit = temp_0_ in
                                          Core_models.Result.Result_Ok pk2_x
                                          <:
                                          Core_models.Result.t_Result
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)
                                                ) (mk_usize 6))
                                            Ark_relations.R1cs.Error.t_SynthesisError)
                                    <:
                                    Core_models.Result.t_Result
                                      (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6))
                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4)))
                                      Ark_relations.R1cs.Error.t_SynthesisError
                                  with
                                  | Core_models.Result.Result_Ok e_pk2_x_var ->
                                    (match
                                        Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4)))
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6))
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          #FStar.Tactics.Typeclasses.solve
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6))
                                          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          #(Prims.unit
                                              -> Core_models.Result.t_Result
                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  Ark_relations.R1cs.Error.t_SynthesisError)
                                          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                              #FStar.Tactics.Typeclasses.solve
                                              cs
                                            <:
                                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4)))
                                          (fun temp_0_ ->
                                              let _:Prims.unit = temp_0_ in
                                              Core_models.Result.Result_Ok pk2_y
                                              <:
                                              Core_models.Result.t_Result
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                        (mk_usize 6)) (mk_usize 6))
                                                Ark_relations.R1cs.Error.t_SynthesisError)
                                        <:
                                        Core_models.Result.t_Result
                                          (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                      (mk_usize 6)) (mk_usize 6))
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4)))
                                          Ark_relations.R1cs.Error.t_SynthesisError
                                      with
                                      | Core_models.Result.Result_Ok e_pk2_y_var ->
                                        let
                                        (_:
                                          Core_models.Slice.Iter.t_Iter
                                          (u32 &
                                            Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4) &
                                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                            Ark_bls12_381_.Curves.G1.t_Config)),
                                        (out:
                                          Core_models.Option.t_Option
                                          (u32 &
                                            Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4) &
                                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                            Ark_bls12_381_.Curves.G1.t_Config)) =
                                          Core_models.Iter.Traits.Iterator.f_find #(Core_models.Slice.Iter.t_Iter
                                              (u32 &
                                                Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4) &
                                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                Ark_bls12_381_.Curves.G1.t_Config))
                                            #FStar.Tactics.Typeclasses.solve
                                            #(
                                                  (u32 &
                                                      Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4) &
                                                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                      Ark_bls12_381_.Curves.G1.t_Config)
                                                -> bool)
                                            (Core_models.Slice.impl__iter #(u32 &
                                                  Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4) &
                                                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                  Ark_bls12_381_.Curves.G1.t_Config)
                                                (Alloc.Vec.impl_1__as_slice self.f_pads
                                                  <:
                                                  t_Slice
                                                  (u32 &
                                                    Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4) &
                                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                    Ark_bls12_381_.Curves.G1.t_Config))
                                              <:
                                              Core_models.Slice.Iter.t_Iter
                                              (u32 &
                                                Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4) &
                                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                Ark_bls12_381_.Curves.G1.t_Config))
                                            (fun temp_0_ ->
                                                let
                                                (pid: u32),
                                                (_:
                                                  Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)),
                                                (_:
                                                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                  Ark_bls12_381_.Curves.G1.t_Config) =
                                                  temp_0_
                                                in
                                                pid =. peer_id <: bool)
                                        in
                                        (match
                                            out
                                            <:
                                            Core_models.Option.t_Option
                                            (u32 &
                                              Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4) &
                                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                              Ark_bls12_381_.Curves.G1.t_Config)
                                          with
                                          | Core_models.Option.Option_Some
                                            (_, r_value, r_commitment) ->
                                            let r_x:Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6) =
                                              if
                                                r_commitment
                                                  .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                              then
                                                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  ()
                                              else
                                                r_commitment
                                                  .Ark_ec.Models.Short_weierstrass.Affine.f_x
                                            in
                                            let r_y:Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6))
                                              (mk_usize 6) =
                                              if
                                                r_commitment
                                                  .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                              then
                                                Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  ()
                                              else
                                                r_commitment
                                                  .Ark_ec.Models.Short_weierstrass.Affine.f_y
                                            in
                                            (match
                                                Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4)))
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                          (mk_usize 6)) (mk_usize 6))
                                                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)))
                                                  #(Prims.unit
                                                      -> Core_models.Result.t_Result
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                  (mk_usize 6)) (mk_usize 6))
                                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                (mk_usize 4)) (mk_usize 4)))
                                                      #FStar.Tactics.Typeclasses.solve
                                                      cs
                                                    <:
                                                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4)))
                                                  (fun temp_0_ ->
                                                      let _:Prims.unit = temp_0_ in
                                                      Core_models.Result.Result_Ok r_x
                                                      <:
                                                      Core_models.Result.t_Result
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                (mk_usize 6)) (mk_usize 6))
                                                        Ark_relations.R1cs.Error.t_SynthesisError)
                                                <:
                                                Core_models.Result.t_Result
                                                  (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4)))
                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                              with
                                              | Core_models.Result.Result_Ok e_r_x_var ->
                                                (match
                                                    Ark_r1cs_std.Alloc.f_new_input #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                  (mk_usize 6)) (mk_usize 6))
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4)))
                                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4))
                                                      #FStar.Tactics.Typeclasses.solve
                                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6))
                                                      #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                (mk_usize 4)) (mk_usize 4)))
                                                      #(Prims.unit
                                                          -> Core_models.Result.t_Result
                                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                      (mk_usize 6)) (mk_usize 6))
                                                              Ark_relations.R1cs.Error.t_SynthesisError
                                                      )
                                                      (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          #FStar.Tactics.Typeclasses.solve
                                                          cs
                                                        <:
                                                        Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                (mk_usize 4)) (mk_usize 4)))
                                                      (fun temp_0_ ->
                                                          let _:Prims.unit = temp_0_ in
                                                          Core_models.Result.Result_Ok r_y
                                                          <:
                                                          Core_models.Result.t_Result
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                    (mk_usize 6)) (mk_usize 6))
                                                            Ark_relations.R1cs.Error.t_SynthesisError
                                                      )
                                                    <:
                                                    Core_models.Result.t_Result
                                                      (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                  (mk_usize 6)) (mk_usize 6))
                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4)))
                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                  with
                                                  | Core_models.Result.Result_Ok e_r_y_var ->
                                                    (match
                                                        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4))
                                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4))
                                                          #FStar.Tactics.Typeclasses.solve
                                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                  (mk_usize 4)) (mk_usize 4))
                                                          #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          #(Prims.unit
                                                              -> Core_models.Result.t_Result
                                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                          (mk_usize 4)) (mk_usize 4)
                                                                  )
                                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                                          )
                                                          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4)))
                                                              #FStar.Tactics.Typeclasses.solve
                                                              cs
                                                            <:
                                                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          (fun temp_0_ ->
                                                              let _:Prims.unit = temp_0_ in
                                                              Core_models.Result.Result_Ok r_value
                                                              <:
                                                              Core_models.Result.t_Result
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4))
                                                                Ark_relations.R1cs.Error.t_SynthesisError
                                                          )
                                                        <:
                                                        Core_models.Result.t_Result
                                                          (Ark_r1cs_std.Fields.Fp.t_FpVar
                                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                    (mk_usize 4)) (mk_usize 4)))
                                                          Ark_relations.R1cs.Error.t_SynthesisError
                                                      with
                                                      | Core_models.Result.Result_Ok r_var ->
                                                        let dh:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                        Ark_bls12_381_.Curves.G1.t_Config =
                                                          Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                                              Ark_bls12_381_.Curves.G1.t_Config)
                                                            #FStar.Tactics.Typeclasses.solve
                                                            (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                                  Ark_bls12_381_.Curves.G1.t_Config)
                                                                #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4))
                                                                #FStar.Tactics.Typeclasses.solve
                                                                peer_pk
                                                                self.f_sk1
                                                              <:
                                                              Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                                              Ark_bls12_381_.Curves.G1.t_Config)
                                                        in
                                                        let dh_x:Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6) =
                                                          if
                                                            dh
                                                              .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                                          then
                                                            Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                      (mk_usize 6)) (mk_usize 6))
                                                              #FStar.Tactics.Typeclasses.solve
                                                              ()
                                                          else
                                                            dh
                                                              .Ark_ec.Models.Short_weierstrass.Affine.f_x
                                                        in
                                                        let dh_y:Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                              (mk_usize 6)) (mk_usize 6) =
                                                          if
                                                            dh
                                                              .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                                                          then
                                                            Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                      (mk_usize 6)) (mk_usize 6))
                                                              #FStar.Tactics.Typeclasses.solve
                                                              ()
                                                          else
                                                            dh
                                                              .Ark_ec.Models.Short_weierstrass.Affine.f_y
                                                        in
                                                        (match
                                                            Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                          (mk_usize 6)) (mk_usize 6)
                                                                  )
                                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                          (mk_usize 4)) (mk_usize 4)
                                                                  ))
                                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                      (mk_usize 6)) (mk_usize 6))
                                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                      (mk_usize 4)) (mk_usize 4))
                                                              #FStar.Tactics.Typeclasses.solve
                                                              #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                      Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                      (mk_usize 6)) (mk_usize 6))
                                                              #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4)))
                                                              #(Prims.unit
                                                                  -> Core_models.Result.t_Result
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                              (mk_usize 6))
                                                                          (mk_usize 6))
                                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                              )
                                                              (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                            (mk_usize 4))
                                                                        (mk_usize 4)))
                                                                  #FStar.Tactics.Typeclasses.solve
                                                                  cs
                                                                <:
                                                                Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4)))
                                                              (fun temp_0_ ->
                                                                  let _:Prims.unit = temp_0_ in
                                                                  Core_models.Result.Result_Ok dh_x
                                                                  <:
                                                                  Core_models.Result.t_Result
                                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                            Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                            (mk_usize 6))
                                                                        (mk_usize 6))
                                                                    Ark_relations.R1cs.Error.t_SynthesisError
                                                              )
                                                            <:
                                                            Core_models.Result.t_Result
                                                              (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                          (mk_usize 6)) (mk_usize 6)
                                                                  )
                                                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                          (mk_usize 4)) (mk_usize 4)
                                                                  ))
                                                              Ark_relations.R1cs.Error.t_SynthesisError
                                                          with
                                                          | Core_models.Result.Result_Ok e_dh_x_var ->
                                                            (match
                                                                Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                              (mk_usize 6))
                                                                          (mk_usize 6))
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                              (mk_usize 4))
                                                                          (mk_usize 4)))
                                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                          (mk_usize 6)) (mk_usize 6)
                                                                  )
                                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                          (mk_usize 4)) (mk_usize 4)
                                                                  )
                                                                  #FStar.Tactics.Typeclasses.solve
                                                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                          Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                          (mk_usize 6)) (mk_usize 6)
                                                                  )
                                                                  #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                            (mk_usize 4))
                                                                        (mk_usize 4)))
                                                                  #(Prims.unit
                                                                      -> Core_models.Result.t_Result
                                                                          (Ark_ff.Fields.Models.Fp.t_Fp
                                                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                                  Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                                  (mk_usize 6))
                                                                              (mk_usize 6))
                                                                          Ark_relations.R1cs.Error.t_SynthesisError
                                                                  )
                                                                  (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                                Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                                (mk_usize 4))
                                                                            (mk_usize 4)))
                                                                      #FStar.Tactics.Typeclasses.solve
                                                                      cs
                                                                    <:
                                                                    Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                                                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                            (mk_usize 4))
                                                                        (mk_usize 4)))
                                                                  (fun temp_0_ ->
                                                                      let _:Prims.unit = temp_0_ in
                                                                      Core_models.Result.Result_Ok
                                                                      dh_y
                                                                      <:
                                                                      Core_models.Result.t_Result
                                                                        (Ark_ff.Fields.Models.Fp.t_Fp
                                                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                                Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                                (mk_usize 6))
                                                                            (mk_usize 6))
                                                                        Ark_relations.R1cs.Error.t_SynthesisError
                                                                  )
                                                                <:
                                                                Core_models.Result.t_Result
                                                                  (Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fq.t_FqConfig
                                                                              (mk_usize 6))
                                                                          (mk_usize 6))
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                              (mk_usize 4))
                                                                          (mk_usize 4)))
                                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                                              with
                                                              | Core_models.Result.Result_Ok
                                                                e_dh_y_var ->
                                                                let _:Ark_r1cs_std.Fields.Fp.t_FpVar
                                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                        (mk_usize 4)) (mk_usize 4))
                                                                =
                                                                  Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                              (mk_usize 4))
                                                                          (mk_usize 4)))
                                                                    #(Ark_r1cs_std.Fields.Fp.t_FpVar
                                                                      (Ark_ff.Fields.Models.Fp.t_Fp
                                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                                              (mk_usize 4))
                                                                          (mk_usize 4)))
                                                                    #FStar.Tactics.Typeclasses.solve
                                                                    sk1_var
                                                                    r_var
                                                                in
                                                                Core_models.Ops.Control_flow.ControlFlow_Continue
                                                                ()
                                                                <:
                                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                                                      (Core_models.Result.t_Result
                                                                          Prims.unit
                                                                          Ark_relations.R1cs.Error.t_SynthesisError
                                                                      ) (Prims.unit & Prims.unit))
                                                                  Prims.unit
                                                              | Core_models.Result.Result_Err err ->
                                                                Core_models.Ops.Control_flow.ControlFlow_Break
                                                                (Core_models.Ops.Control_flow.ControlFlow_Break
                                                                  (Core_models.Result.Result_Err err
                                                                    <:
                                                                    Core_models.Result.t_Result
                                                                      Prims.unit
                                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                                  )
                                                                  <:
                                                                  Core_models.Ops.Control_flow.t_ControlFlow
                                                                    (Core_models.Result.t_Result
                                                                        Prims.unit
                                                                        Ark_relations.R1cs.Error.t_SynthesisError
                                                                    ) (Prims.unit & Prims.unit))
                                                                <:
                                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                                                      (Core_models.Result.t_Result
                                                                          Prims.unit
                                                                          Ark_relations.R1cs.Error.t_SynthesisError
                                                                      ) (Prims.unit & Prims.unit))
                                                                  Prims.unit)
                                                          | Core_models.Result.Result_Err err ->
                                                            Core_models.Ops.Control_flow.ControlFlow_Break
                                                            (Core_models.Ops.Control_flow.ControlFlow_Break
                                                              (Core_models.Result.Result_Err err
                                                                <:
                                                                Core_models.Result.t_Result
                                                                  Prims.unit
                                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                                              )
                                                              <:
                                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                                (Core_models.Result.t_Result
                                                                    Prims.unit
                                                                    Ark_relations.R1cs.Error.t_SynthesisError
                                                                ) (Prims.unit & Prims.unit))
                                                            <:
                                                            Core_models.Ops.Control_flow.t_ControlFlow
                                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                                  (Core_models.Result.t_Result
                                                                      Prims.unit
                                                                      Ark_relations.R1cs.Error.t_SynthesisError
                                                                  ) (Prims.unit & Prims.unit))
                                                              Prims.unit)
                                                      | Core_models.Result.Result_Err err ->
                                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                                          (Core_models.Result.Result_Err err
                                                            <:
                                                            Core_models.Result.t_Result Prims.unit
                                                              Ark_relations.R1cs.Error.t_SynthesisError
                                                          )
                                                          <:
                                                          Core_models.Ops.Control_flow.t_ControlFlow
                                                            (Core_models.Result.t_Result Prims.unit
                                                                Ark_relations.R1cs.Error.t_SynthesisError
                                                            ) (Prims.unit & Prims.unit))
                                                        <:
                                                        Core_models.Ops.Control_flow.t_ControlFlow
                                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                                              (Core_models.Result.t_Result
                                                                  Prims.unit
                                                                  Ark_relations.R1cs.Error.t_SynthesisError
                                                              ) (Prims.unit & Prims.unit))
                                                          Prims.unit)
                                                  | Core_models.Result.Result_Err err ->
                                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                                      (Core_models.Result.Result_Err err
                                                        <:
                                                        Core_models.Result.t_Result Prims.unit
                                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                                      <:
                                                      Core_models.Ops.Control_flow.t_ControlFlow
                                                        (Core_models.Result.t_Result Prims.unit
                                                            Ark_relations.R1cs.Error.t_SynthesisError
                                                        ) (Prims.unit & Prims.unit))
                                                    <:
                                                    Core_models.Ops.Control_flow.t_ControlFlow
                                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                                          (Core_models.Result.t_Result Prims.unit
                                                              Ark_relations.R1cs.Error.t_SynthesisError
                                                          ) (Prims.unit & Prims.unit)) Prims.unit)
                                              | Core_models.Result.Result_Err err ->
                                                Core_models.Ops.Control_flow.ControlFlow_Break
                                                (Core_models.Ops.Control_flow.ControlFlow_Break
                                                  (Core_models.Result.Result_Err err
                                                    <:
                                                    Core_models.Result.t_Result Prims.unit
                                                      Ark_relations.R1cs.Error.t_SynthesisError)
                                                  <:
                                                  Core_models.Ops.Control_flow.t_ControlFlow
                                                    (Core_models.Result.t_Result Prims.unit
                                                        Ark_relations.R1cs.Error.t_SynthesisError)
                                                    (Prims.unit & Prims.unit))
                                                <:
                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                                      (Core_models.Result.t_Result Prims.unit
                                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                                      (Prims.unit & Prims.unit)) Prims.unit)
                                          | _ ->
                                            Core_models.Ops.Control_flow.ControlFlow_Continue ()
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Result.t_Result Prims.unit
                                                      Ark_relations.R1cs.Error.t_SynthesisError)
                                                  (Prims.unit & Prims.unit)) Prims.unit)
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                          (Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result Prims.unit
                                              Ark_relations.R1cs.Error.t_SynthesisError)
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Result.t_Result Prims.unit
                                                Ark_relations.R1cs.Error.t_SynthesisError)
                                            (Prims.unit & Prims.unit))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Result.t_Result Prims.unit
                                                  Ark_relations.R1cs.Error.t_SynthesisError)
                                              (Prims.unit & Prims.unit)) Prims.unit)
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit
                                          Ark_relations.R1cs.Error.t_SynthesisError)
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result Prims.unit
                                            Ark_relations.R1cs.Error.t_SynthesisError)
                                        (Prims.unit & Prims.unit))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Result.t_Result Prims.unit
                                              Ark_relations.R1cs.Error.t_SynthesisError)
                                          (Prims.unit & Prims.unit)) Prims.unit)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Prims.unit
                                  Ark_relations.R1cs.Error.t_SynthesisError) Prims.unit
                          with
                          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                          | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                            Core_models.Result.Result_Ok (() <: Prims.unit)
                            <:
                            Core_models.Result.t_Result Prims.unit
                              Ark_relations.R1cs.Error.t_SynthesisError)
                      | Core_models.Result.Result_Err err ->
                        Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result Prims.unit
                          Ark_relations.R1cs.Error.t_SynthesisError)
                  | Core_models.Result.Result_Err err ->
                    Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
                )
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
  }
