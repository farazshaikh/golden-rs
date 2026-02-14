module Golden_rs.Schnorr_pok
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
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Ark_serialize in
  let open Ark_serialize.Error in
  let open Ark_std.Rand_helper in
  let open Block_buffer in
  let open Borsh.De in
  let open Borsh.Ser in
  let open Digest in
  let open Digest.Core_api in
  let open Digest.Core_api.Ct_variable in
  let open Digest.Core_api.Wrapper in
  let open Digest.Digest in
  let open Generic_array in
  let open Rand.Distributions.Distribution in
  let open Rand.Rng in
  let open Sha2.Core_api in
  let open Std.Io in
  let open Std.Io.Impls in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// A Schnorr proof of knowledge of discrete log: proves knowledge of `sk` such
/// that `PK = g^sk`.
/// Per Appendix F of the Golden paper (IACR 2025/1924), this proof is required
/// when registering an identity public key with the PKI functionality `F_pki`.
/// The proof consists of a commitment `R = g^nonce` and a response
/// `s = nonce + challenge * sk` using the Fiat-Shamir heuristic.
type t_SchnorrPoK = {
  f_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_response:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl_2: Core_models.Clone.t_Clone t_SchnorrPoK =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_SchnorrPoK

unfold
let impl_3 = impl_3'

/// Compute the Fiat-Shamir challenge: `c = H(g || pk || R) mod r`.
/// Uses SHA-256 with domain separator `"golden-schnorr-pok"` to hash the
/// generator, public key, and commitment into a challenge scalar. This
/// converts the interactive Sigma protocol into a non-interactive proof.
let compute_challenge
      (pk commitment:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
  (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
      (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                          Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
      Sha2.t_OidSha256) =
    Digest.Digest.f_new #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
  (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
      (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                          Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
      Sha2.t_OidSha256) =
    Digest.Digest.f_update #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      #(t_Array u8 (mk_usize 18))
      hasher
      (let list =
          [
            mk_u8 103; mk_u8 111; mk_u8 108; mk_u8 100; mk_u8 101; mk_u8 110; mk_u8 45; mk_u8 115;
            mk_u8 99; mk_u8 104; mk_u8 110; mk_u8 111; mk_u8 114; mk_u8 114; mk_u8 45; mk_u8 112;
            mk_u8 111; mk_u8 107
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 18);
        Rust_primitives.Hax.array_of_list 18 list)
  in
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(ark_ec::f_generator(Tuple0)), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "serialize failed"
  in
  let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
  (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
      (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                          Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
      Sha2.t_OidSha256) =
    Digest.Digest.f_update #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      hasher
      buf
  in
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_1__clear #u8 #Alloc.Alloc.t_Global buf
  in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(pk), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "serialize failed"
  in
  let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
  (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
      (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                          Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
      Sha2.t_OidSha256) =
    Digest.Digest.f_update #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      hasher
      buf
  in
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_1__clear #u8 #Alloc.Alloc.t_Global buf
  in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(commitment), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "serialize failed"
  in
  let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
  (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
      (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                          Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
      Sha2.t_OidSha256) =
    Digest.Digest.f_update #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      hasher
      buf
  in
  let hash:Generic_array.t_GenericArray u8
    (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
        Typenum.Bit.t_B0) =
    Digest.Digest.f_finalize #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      hasher
  in
  Ark_ff.Fields.Prime.f_from_le_bytes_mod_order #(Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0))
        #FStar.Tactics.Typeclasses.solve
        hash
      <:
      t_Slice u8)

/// Generate a Schnorr proof of knowledge.
/// Proves: "I know `sk` such that `pk = g^sk`" using the Sigma protocol
/// made non-interactive via the Fiat-Shamir transform:
///   1. Sample nonce `k <- Z_p`
///   2. `R = g^k`
///   3. `c = H(g || pk || R)` (Fiat-Shamir challenge)
///   4. `s = k + c * sk`
///   5. Output `(R, s)`
let prove
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (rng: iimpl_1039969868_)
    : (iimpl_1039969868_ & t_SchnorrPoK) =
  let
  (tmp0: iimpl_1039969868_),
  (out:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Ark_std.Rand_helper.f_rand #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      #iimpl_1039969868_
      rng
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let nonce:Golden_rs.Types.t_SecretScalar = Golden_rs.Types.impl_SecretScalar__new out in
  let commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              #FStar.Tactics.Typeclasses.solve
              ()
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          (Golden_rs.Types.impl_SecretScalar__inner nonce
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let challenge:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    compute_challenge pk commitment
  in
  let response:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Ops.Arith.f_add #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      (Golden_rs.Types.impl_SecretScalar__inner nonce
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          challenge
          sk
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  in
  let hax_temp_output:t_SchnorrPoK =
    { f_commitment = commitment; f_response = response } <: t_SchnorrPoK
  in
  rng, hax_temp_output <: (iimpl_1039969868_ & t_SchnorrPoK)

/// Verify a Schnorr proof of knowledge.
/// Checks the verification equation: `g^s == R + c * PK`
/// where `c = H(g || pk || R)`.
/// This ensures the prover knows `sk` such that `PK = g^sk` without
/// revealing `sk`.
let verify
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (proof: t_SchnorrPoK)
    : bool =
  let challenge:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    compute_challenge pk proof.f_commitment
  in
  let lhs:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              #FStar.Tactics.Typeclasses.solve
              ()
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          proof.f_response
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let rhs:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              #FStar.Tactics.Typeclasses.solve
              proof.f_commitment
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
          (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              pk
              challenge
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  lhs =. rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl: Borsh.Ser.t_BorshSerialize t_SchnorrPoK

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1: Borsh.De.t_BorshDeserialize t_SchnorrPoK

