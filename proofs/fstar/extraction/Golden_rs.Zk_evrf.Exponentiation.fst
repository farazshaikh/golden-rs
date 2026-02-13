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
let impl_PointVar__new_witness
      (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (point: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError =
  let
  (x:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6)),
  (y:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6)) =
    if point.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
    then
      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #FStar.Tactics.Typeclasses.solve
        (),
      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #FStar.Tactics.Typeclasses.solve
        ()
      <:
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    else
      point.Ark_ec.Models.Short_weierstrass.Affine.f_x,
      point.Ark_ec.Models.Short_weierstrass.Affine.f_y
      <:
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
  in
  match
    Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
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
          Core_models.Result.Result_Ok x
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
  | Core_models.Result.Result_Ok hoist62 ->
    (match
        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
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
          cs
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok y
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
      | Core_models.Result.Result_Ok hoist61 ->
        Core_models.Result.Result_Ok ({ f_x = hoist62; f_y = hoist61 } <: t_PointVar)
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError

/// Allocate a G1 point as a public input.
let impl_PointVar__new_input
      (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (point: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError =
  let
  (x:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6)),
  (y:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6)) =
    if point.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
    then
      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #FStar.Tactics.Typeclasses.solve
        (),
      Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #FStar.Tactics.Typeclasses.solve
        ()
      <:
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    else
      point.Ark_ec.Models.Short_weierstrass.Affine.f_x,
      point.Ark_ec.Models.Short_weierstrass.Affine.f_y
      <:
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6) &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
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
          Core_models.Result.Result_Ok x
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
  | Core_models.Result.Result_Ok hoist65 ->
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
          cs
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok y
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
      | Core_models.Result.Result_Ok hoist64 ->
        Core_models.Result.Result_Ok ({ f_x = hoist65; f_y = hoist64 } <: t_PointVar)
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError

/// Enforce that this point equals another point.
let impl_PointVar__enforce_equal (self other: t_PointVar)
    : Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError =
  match
    Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      self.f_x
      other.f_x
    <:
    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
  with
  | Core_models.Result.Result_Ok _ ->
    (match
        Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          self.f_y
          other.f_y
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
      with
      | Core_models.Result.Result_Ok _ ->
        Core_models.Result.Result_Ok (() <: Prims.unit)
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError

/// Point addition using the chord rule (`P1 != P2`, `P1 != -P2`).
/// Given `P1 = (x1, y1)` and `P2 = (x2, y2)` with `x1 != x2`:
///   `s = (y2 - y1) / (x2 - x1)`
///   `x3 = s^2 - x1 - x2`
///   `y3 = s * (x1 - x3) - y1`
/// The prover supplies the slope `s` as a witness; the circuit constrains:
///   1. `s * (x2 - x1) = y2 - y1`
///   2. `x3 = s^2 - x1 - x2`
///   3. `y3 = s * (x1 - x3) - y1`
let point_add
      (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (p1 p2: t_PointVar)
      (expected_result:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError =
  match
    impl_PointVar__new_witness (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
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
      expected_result
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
  with
  | Core_models.Result.Result_Ok result ->
    let x1_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p1.f_x
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let y1_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p1.f_y
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let x2_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p2.f_x
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let y2_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p2.f_y
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let s_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      if x2_val <>. x1_val
      then
        Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #FStar.Tactics.Typeclasses.solve
              y2_val
              y1_val
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Core_models.Option.impl__unwrap #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.f_inverse #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #FStar.Tactics.Typeclasses.solve
                      x2_val
                      x1_val
                    <:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                <:
                Core_models.Option.t_Option
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)))
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
      else
        Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #FStar.Tactics.Typeclasses.solve
          ()
    in
    (match
        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
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
          cs
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok s_val
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
      | Core_models.Result.Result_Ok s ->
        let dx:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            p2.f_x
            p1.f_x
        in
        let dy:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            p2.f_y
            p1.f_y
        in
        let s_times_dx:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            s
            dx
        in
        (match
            Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              s_times_dx
              dy
            <:
            Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
          with
          | Core_models.Result.Result_Ok _ ->
            let s_sq:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                s
                s
            in
            let expected_x3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                (Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    s_sq
                    p1.f_x
                  <:
                  Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                p2.f_x
            in
            (match
                Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  result.f_x
                  expected_x3
                <:
                Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
              with
              | Core_models.Result.Result_Ok _ ->
                let x1_minus_x3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    p1.f_x
                    result.f_x
                in
                let s_times_diff:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    s
                    x1_minus_x3
                in
                let expected_y3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    s_times_diff
                    p1.f_y
                in
                (match
                    Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      result.f_y
                      expected_y3
                    <:
                    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
                  with
                  | Core_models.Result.Result_Ok _ ->
                    Core_models.Result.Result_Ok result
                    <:
                    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
                  | Core_models.Result.Result_Err err ->
                    Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
                )
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError

/// Point doubling using the tangent rule.
/// For BLS12-381 G1: `y^2 = x^3 + 4`, so the curve parameter `a = 0`.
///   `s = 3*x1^2 / (2*y1)`
///   `x3 = s^2 - 2*x1`
///   `y3 = s * (x1 - x3) - y1`
/// The prover supplies `s` as a witness; the circuit constrains:
///   1. `s * (2 * y1) = 3 * x1^2`
///   2. `x3 = s^2 - 2*x1`
///   3. `y3 = s * (x1 - x3) - y1`
let point_double
      (cs:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (p: t_PointVar)
      (expected_result:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError =
  match
    impl_PointVar__new_witness (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
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
      expected_result
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
  with
  | Core_models.Result.Result_Ok result ->
    let x_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p.f_x
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let y_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Result.impl__unwrap_or #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #Ark_relations.R1cs.Error.t_SynthesisError
        (Ark_r1cs_std.R1cs_var.f_value #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            p.f_y
          <:
          Core_models.Result.t_Result
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            Ark_relations.R1cs.Error.t_SynthesisError)
        (Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    in
    let three:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #u64
        #FStar.Tactics.Typeclasses.solve
        (mk_u64 3)
    in
    let two:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
        #u64
        #FStar.Tactics.Typeclasses.solve
        (mk_u64 2)
    in
    let s_val:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig
          (mk_usize 6)) (mk_usize 6) =
      if
        ~.(Num_traits.Identities.f_is_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            y_val
          <:
          bool)
      then
        Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              #FStar.Tactics.Typeclasses.solve
              (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  three
                  x_val
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              x_val
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Core_models.Option.impl__unwrap #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.f_inverse #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  #FStar.Tactics.Typeclasses.solve
                  (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      #FStar.Tactics.Typeclasses.solve
                      two
                      y_val
                    <:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                <:
                Core_models.Option.t_Option
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6)))
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
      else
        Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #FStar.Tactics.Typeclasses.solve
          ()
    in
    (match
        Ark_r1cs_std.Alloc.f_new_witness #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
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
          cs
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              Core_models.Result.Result_Ok s_val
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
      | Core_models.Result.Result_Ok s ->
        let two_y:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_add #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            p.f_y
            p.f_y
        in
        let s_times_2y:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            s
            two_y
        in
        let x_sq:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            p.f_x
            p.f_x
        in
        let three_x_sq:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
          Core_models.Ops.Arith.f_add #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            #FStar.Tactics.Typeclasses.solve
            (Core_models.Ops.Arith.f_add #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                x_sq
                x_sq
              <:
              Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            x_sq
        in
        (match
            Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              s_times_2y
              three_x_sq
            <:
            Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
          with
          | Core_models.Result.Result_Ok _ ->
            let s_sq:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                s
                s
            in
            let two_x:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              Core_models.Ops.Arith.f_add #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                p.f_x
                p.f_x
            in
            let expected_x3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #FStar.Tactics.Typeclasses.solve
                s_sq
                two_x
            in
            (match
                Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  result.f_x
                  expected_x3
                <:
                Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
              with
              | Core_models.Result.Result_Ok _ ->
                let x_minus_x3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    p.f_x
                    result.f_x
                in
                let s_times_diff:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_mul #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    s
                    x_minus_x3
                in
                let expected_y3:Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
                  Core_models.Ops.Arith.f_sub #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    #FStar.Tactics.Typeclasses.solve
                    s_times_diff
                    p.f_y
                in
                (match
                    Ark_r1cs_std.Eq.f_enforce_equal #(Ark_r1cs_std.Fields.Emulated_fp.Field_var.t_EmulatedFpVar
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      result.f_y
                      expected_y3
                    <:
                    Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError
                  with
                  | Core_models.Result.Result_Ok _ ->
                    Core_models.Result.Result_Ok result
                    <:
                    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
                  | Core_models.Result.Result_Err err ->
                    Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
                )
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_PointVar Ark_relations.R1cs.Error.t_SynthesisError
