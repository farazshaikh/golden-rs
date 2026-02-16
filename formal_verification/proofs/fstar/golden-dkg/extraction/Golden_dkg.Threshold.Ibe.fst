module Golden_dkg.Threshold.Ibe
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves in
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Curves.G2 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fq12 in
  let open Ark_bls12_381_.Fields.Fq2 in
  let open Ark_bls12_381_.Fields.Fq6 in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec in
  let open Ark_ec.Models.Bls12 in
  let open Ark_ec.Models.Bls12.G1 in
  let open Ark_ec.Models.Bls12.G2 in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ec.Pairing in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields.Models.Cubic_extension in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Models.Fp12_2over3over2 in
  let open Ark_ff.Fields.Models.Fp2 in
  let open Ark_ff.Fields.Models.Fp6_3over2 in
  let open Ark_ff.Fields.Models.Quadratic_extension in
  let open Ark_serialize.Error in
  let open Ark_std.Rand_helper in
  let open Block_buffer in
  let open Digest in
  let open Digest.Core_api in
  let open Digest.Core_api.Ct_variable in
  let open Digest.Core_api.Wrapper in
  let open Digest.Digest in
  let open Generic_array in
  let open Rand.Distributions.Distribution in
  let open Rand.Rng in
  let open Rand_chacha.Chacha in
  let open Rand_core in
  let open Sha2.Core_api in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// Transport public key for encrypted key delivery.
/// `tpk = g2^tsk` (in our convention; paper Section 2, p.6 has tpk in G1).
/// **Paper**: Section 2, p.6: "TKG() -> (tpk, tsk): A transport key generation
/// algorithm that a user can use to generate a transport public key tpk and
/// corresponding secret key tsk."
/// **NCC Audit Finding XPJ**: TransportSecretKey must be zeroized on drop
/// (see NCC Group VetKeys report, Section 4, p.16-17).
type t_TransportPublicKey =
  | TransportPublicKey :
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
    -> t_TransportPublicKey

let impl_1: Core_models.Clone.t_Clone t_TransportPublicKey =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_TransportPublicKey

unfold
let impl_2 = impl_2'

/// Transport secret key: scalar `tsk` such that `tpk = g2^tsk`.
/// **Zeroization**: Overwritten with zero on drop to prevent secret leakage
/// through memory inspection (NCC Audit Finding XPJ, p.16-17).
/// **Paper**: Section 2, p.6: part of TKG() output.
type t_TransportSecretKey =
  | TransportSecretKey :
      Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
    -> t_TransportSecretKey

let impl_3: Core_models.Clone.t_Clone t_TransportSecretKey =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Ops.Drop.t_Drop t_TransportSecretKey =
  {
    f_drop_pre = (fun (self: t_TransportSecretKey) -> true);
    f_drop_post = (fun (self: t_TransportSecretKey) (out: t_TransportSecretKey) -> true);
    f_drop
    =
    fun (self: t_TransportSecretKey) ->
      let self:t_TransportSecretKey =
        {
          self with
          _0
          =
          Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #u64
            #FStar.Tactics.Typeclasses.solve
            (mk_u64 0)
        }
        <:
        t_TransportSecretKey
      in
      self
  }

/// Encrypted key share from one node.
/// **Paper**: Section 5.3, protocol pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, encsign, m, tpk), S_i computes sigma_i = H(m)^{sk_i},
///  encrypts sigma_i as (C1, C2, C3) = (g1^t, g2^t, tpk^t * sigma_i)"
/// In our G1-pk/G2-sig convention, C3 is in G2 (paper has it in G1).
/// The pairing verification equations are adapted accordingly.
type t_EncryptedKeyShare = {
  f_c1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_c2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config;
  f_c3:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config;
  f_signer:u32
}

let impl_4: Core_models.Clone.t_Clone t_EncryptedKeyShare =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_EncryptedKeyShare

unfold
let impl_5 = impl_5'

/// Combined encrypted vetKey after Lagrange interpolation of shares.
/// **Paper**: Section 5.3, Figure 9 (p.27): "When it received t valid such
/// es_i = (C_{i,1}, C_{i,2}, C_{i,3}) from different servers S_i, i in S,
/// it computes es = (C1, C2, C3) = (prod C_{i,1}^{lambda_i}, ...)"
/// Verifiable via pairing: `e(group_pk, H(id)) + e(C1, tpk) = e(g1, C3)`
/// (adapted from paper's `e(C2, g2) = e(C1, tpk_2) * e(H(m), pk)`)
type t_EncryptedVetKey = {
  f_c1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_c2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config;
  f_c3:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
}

let impl_6: Core_models.Clone.t_Clone t_EncryptedVetKey =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Fmt.t_Debug t_EncryptedVetKey

unfold
let impl_7 = impl_7'

/// A vetKey: the BLS signature on an identity, used as IBE decryption key.
/// **Paper**: Section 2, p.6: "Recover(mpk, id, tsk, ek) -> K: A recovery
/// algorithm that enables the user to recover the derived key K for identity
/// id from the verified encrypted key ek using the transport secret key tsk."
/// In our convention: `vetkey = H(id)^sk` is a **G2** point (paper has G1).
/// This is both a valid BLS signature (verifiable via pairing) and the
/// decryption key for Boneh-Franklin IBE ciphertexts encrypted to `id`.
/// **Paper Section 3, p.7**: "A signature on a message m is sigma = H(m)^{sk}"
/// -- the vetKey IS the BLS signature on the identity string.
type t_VetKey =
  | VetKey : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
    -> t_VetKey

let impl_8: Core_models.Clone.t_Clone t_VetKey =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Fmt.t_Debug t_VetKey

unfold
let impl_9 = impl_9'

/// Boneh-Franklin IBE ciphertext with Fujisaki-Okamoto CCA transform.
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, encrypt, mpk', id, m), P checks that m in {0,1}^l.
///  It calls H(id) to obtain h. It then chooses s <- {0,1}^kappa,
///  sets t = H3(s, m), and computes C = (g2^t, s XOR H2(e(h, mpk')^t), m XOR H4(s))"
/// In our convention, `u` is in G1 (paper has G2) because mpk is in G1 and
/// the pairing `e(mpk, H(id))` requires first arg in G1.
/// **Security**: Theorem 7 (p.32): "If the co-BDH problem is hard in (G1, G2)
/// and H2, H3, H4 are modeled as random oracles, then pi_vetibe securely
/// realizes F_vetibe"
type t_IBECiphertext = {
  f_u:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_v:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_w:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

let impl_10: Core_models.Clone.t_Clone t_IBECiphertext =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core_models.Fmt.t_Debug t_IBECiphertext

unfold
let impl_11 = impl_11'

/// Hash identity to G2 for IBE. Domain-separated from beacon hashing.
/// **Paper**: Section 3, p.7: "Let H: {0,1}* -> G1 be a hash function,
/// modeled as a random oracle." In our convention we hash to G2 instead.
/// **Paper**: Section 4.1, p.9: Used as the message space for BLS signatures
/// that serve as IBE decryption keys.
/// Domain separation prefix "vetkeys-ibe-identity:" ensures this hash is
/// independent from the beacon's `hash_to_g2` (which uses no prefix).
/// This separation is required by Theorem 11 / Corollary 1 (p.42-46)
/// for safe single-key composition of IBE with signatures and VRF.
/// Uses SHA-256 -> ChaCha8Rng -> G2Projective::rand for deterministic
/// hash-to-curve.
let hash_identity_to_g2 (identity: t_Slice u8)
    : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
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
      #(t_Array u8 (mk_usize 21))
      hasher
      (let list =
          [
            mk_u8 118; mk_u8 101; mk_u8 116; mk_u8 107; mk_u8 101; mk_u8 121; mk_u8 115; mk_u8 45;
            mk_u8 105; mk_u8 98; mk_u8 101; mk_u8 45; mk_u8 105; mk_u8 100; mk_u8 101; mk_u8 110;
            mk_u8 116; mk_u8 105; mk_u8 116; mk_u8 121; mk_u8 58
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 21);
        Rust_primitives.Hax.array_of_list 21 list)
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
      #(t_Slice u8)
      hasher
      identity
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
  let seed:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let seed:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      seed
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
  in
  let rng:Rand_chacha.Chacha.t_ChaCha8Rng =
    Rand_core.f_from_seed #Rand_chacha.Chacha.t_ChaCha8Rng #FStar.Tactics.Typeclasses.solve seed
  in
  let
  (tmp0: Rand_chacha.Chacha.t_ChaCha8Rng),
  (out: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config) =
    Ark_std.Rand_helper.f_rand #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #Rand_chacha.Chacha.t_ChaCha8Rng
      rng
  in
  let rng:Rand_chacha.Chacha.t_ChaCha8Rng = tmp0 in
  Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
      Ark_bls12_381_.Curves.G2.t_Config)
    #FStar.Tactics.Typeclasses.solve
    out

/// H2: Hash pairing target element to 32-byte mask for seed encryption.
/// **Paper**: Section 6.2, Figure 11 (p.31): "H2" is one of the random
/// oracles in the Boneh-Franklin FullIdent scheme. Maps G_T -> {0,1}^n
/// where n = 256 bits (our seed length).
/// Domain separation: "vetkeys-ibe-h2:" (Corollary 1, p.46).
let hash_h2
      (gt:
          Ark_ff.Fields.Models.Quadratic_extension.t_QuadExtField
          (Ark_ff.Fields.Models.Fp12_2over3over2.t_Fp12ConfigWrapper
            Ark_bls12_381_.Fields.Fq12.t_Fq12Config))
    : t_Array u8 (mk_usize 32) =
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(deref(gt)), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "GT serialize"
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
      #(t_Array u8 (mk_usize 15))
      hasher
      (let list =
          [
            mk_u8 118; mk_u8 101; mk_u8 116; mk_u8 107; mk_u8 101; mk_u8 121; mk_u8 115; mk_u8 45;
            mk_u8 105; mk_u8 98; mk_u8 101; mk_u8 45; mk_u8 104; mk_u8 50; mk_u8 58
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 15);
        Rust_primitives.Hax.array_of_list 15 list)
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
  let out:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let out:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      out
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
          (Digest.Digest.f_finalize #(Digest.Core_api.Wrapper.t_CoreWrapper
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
            <:
            Generic_array.t_GenericArray u8
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt
                                  (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0))
        <:
        t_Slice u8)
  in
  out

/// H3: Hash (seed, message) to scalar for Fujisaki-Okamoto CCA transform.
/// **Paper**: Section 6.2, Figure 11 (p.31): "sets t = H3(s, m)".
/// This derandomization step converts the CPA-secure BasicIdent into the
/// CCA-secure FullIdent scheme [BF01]. The CCA check in `ibe_decrypt`
/// recomputes t and verifies u == g1^t.
/// Maps: {0,1}^256 x {0,1}^* -> Z_q (scalar field).
/// Domain separation: "vetkeys-ibe-h3:".
let hash_h3 (seed: t_Array u8 (mk_usize 32)) (message: t_Slice u8)
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
      #(t_Array u8 (mk_usize 15))
      hasher
      (let list =
          [
            mk_u8 118; mk_u8 101; mk_u8 116; mk_u8 107; mk_u8 101; mk_u8 121; mk_u8 115; mk_u8 45;
            mk_u8 105; mk_u8 98; mk_u8 101; mk_u8 45; mk_u8 104; mk_u8 51; mk_u8 58
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 15);
        Rust_primitives.Hax.array_of_list 15 list)
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
      #(t_Array u8 (mk_usize 32))
      hasher
      seed
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
      #(t_Slice u8)
      hasher
      message
  in
  let s:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let s:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      s
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
          (Digest.Digest.f_finalize #(Digest.Core_api.Wrapper.t_CoreWrapper
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
            <:
            Generic_array.t_GenericArray u8
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt
                                  (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0))
        <:
        t_Slice u8)
  in
  let rng:Rand_chacha.Chacha.t_ChaCha8Rng =
    Rand_core.f_from_seed #Rand_chacha.Chacha.t_ChaCha8Rng #FStar.Tactics.Typeclasses.solve s
  in
  let
  (tmp0: Rand_chacha.Chacha.t_ChaCha8Rng),
  (out:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Ark_std.Rand_helper.f_rand #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      #Rand_chacha.Chacha.t_ChaCha8Rng
      rng
  in
  let rng:Rand_chacha.Chacha.t_ChaCha8Rng = tmp0 in
  out

/// H4: Hash seed to variable-length byte mask for message encryption.
/// **Paper**: Section 6.2, Figure 11 (p.31): "m XOR H4(s)".
/// Maps: {0,1}^256 -> {0,1}^l where l = message length.
/// Implemented as chained SHA-256 blocks (counter mode) to support
/// arbitrary-length messages. The NCC audit (Finding RVN, p.9-11)
/// notes that very large messages cause proportional heap allocation;
/// for large payloads, prefer hybrid encryption (IBE for key, AES-GCM for data).
/// Domain separation: "vetkeys-ibe-h4:".
let hash_h4 (seed: t_Array u8 (mk_usize 32)) (len: usize) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let result:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__with_capacity #u8 len in
  let counter:u32 = mk_u32 0 in
  let (counter: u32), (result: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (counter: u32), (result: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) = temp_0_ in
          true)
      (fun temp_0_ ->
          let (counter: u32), (result: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) = temp_0_ in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result <: usize) <. len <: bool)
      (fun temp_0_ ->
          let (counter: u32), (result: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      (counter, result <: (u32 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      (fun temp_0_ ->
          let (counter: u32), (result: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) = temp_0_ in
          let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
          (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt
                                  (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0)
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
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0)
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
              #(t_Array u8 (mk_usize 15))
              hasher
              (let list =
                  [
                    mk_u8 118; mk_u8 101; mk_u8 116; mk_u8 107; mk_u8 101; mk_u8 121; mk_u8 115;
                    mk_u8 45; mk_u8 105; mk_u8 98; mk_u8 101; mk_u8 45; mk_u8 104; mk_u8 52;
                    mk_u8 58
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 15);
                Rust_primitives.Hax.array_of_list 15 list)
          in
          let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
          (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt
                                  (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0)
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
              #(t_Array u8 (mk_usize 32))
              hasher
              seed
          in
          let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
          (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt
                                  (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                  Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                      Typenum.Bit.t_B0) Typenum.Bit.t_B0)
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
              #(t_Array u8 (mk_usize 4))
              hasher
              (Core_models.Num.impl_u32__to_le_bytes counter <: t_Array u8 (mk_usize 4))
          in
          let block:Generic_array.t_GenericArray u8
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0) =
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
          let take:usize =
            Core_models.Cmp.min #usize
              (mk_usize 32)
              (len -! (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global result <: usize) <: usize)
          in
          let result:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_2__extend_from_slice #u8
              #Alloc.Alloc.t_Global
              result
              ((Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt
                                            (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm
                                                Typenum.Bit.t_B1) Typenum.Bit.t_B0) Typenum.Bit.t_B0
                                    ) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0))
                    #FStar.Tactics.Typeclasses.solve
                    block
                  <:
                  t_Slice u8).[ { Core_models.Ops.Range.f_end = take }
                  <:
                  Core_models.Ops.Range.t_RangeTo usize ]
                <:
                t_Slice u8)
          in
          let counter:u32 = counter +! mk_u32 1 in
          counter, result <: (u32 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
  in
  result

let xor_bytes (a b: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    match
      Core_models.Slice.impl__len #u8 a, Core_models.Slice.impl__len #u8 b <: (usize & usize)
    with
    | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
  in
  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Iter.Adapters.Zip.t_Zip (Core_models.Slice.Iter.t_Iter u8)
            (Core_models.Slice.Iter.t_Iter u8)) ((u8 & u8) -> u8))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Iter.Adapters.Zip.t_Zip
            (Core_models.Slice.Iter.t_Iter u8) (Core_models.Slice.Iter.t_Iter u8))
        #FStar.Tactics.Typeclasses.solve
        #u8
        #((u8 & u8) -> u8)
        (Core_models.Iter.Traits.Iterator.f_zip #(Core_models.Slice.Iter.t_Iter u8)
            #FStar.Tactics.Typeclasses.solve
            #(Core_models.Slice.Iter.t_Iter u8)
            (Core_models.Slice.impl__iter #u8 a <: Core_models.Slice.Iter.t_Iter u8)
            (Core_models.Slice.impl__iter #u8 b <: Core_models.Slice.Iter.t_Iter u8)
          <:
          Core_models.Iter.Adapters.Zip.t_Zip (Core_models.Slice.Iter.t_Iter u8)
            (Core_models.Slice.Iter.t_Iter u8))
        (fun temp_0_ ->
            let (x: u8), (y: u8) = temp_0_ in
            x ^. y <: u8)
      <:
      Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Iter.Adapters.Zip.t_Zip (Core_models.Slice.Iter.t_Iter u8)
            (Core_models.Slice.Iter.t_Iter u8)) ((u8 & u8) -> u8))

/// Generate transport key pair: `tpk = g2^tsk`.
/// **Paper**: Section 2, p.6: "TKG() -> (tpk, tsk): A transport key generation
/// algorithm that a user can use to generate a transport public key tpk and
/// corresponding secret key tsk."
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27): "On (sid,
/// transport-keygen), U chooses tsk <- Z_q, computes tpk <- g1^{tsk}"
/// (we use g2 instead of g1 for our G1-pk/G2-sig convention).
/// The transport key is ephemeral -- it only needs to be held for the
/// duration of one vetKD evaluation (Paper Section 2, p.7).
let transport_keygen
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng v_R)
      (rng: v_R)
    : (v_R & (t_TransportPublicKey & t_TransportSecretKey)) =
  let
  (tmp0: v_R),
  (out:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Ark_std.Rand_helper.f_rand #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      #v_R
      rng
  in
  let rng:v_R = tmp0 in
  let tsk:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    out
  in
  let tpk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G2.t_Config)
              #FStar.Tactics.Typeclasses.solve
              ()
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          tsk
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  let hax_temp_output:(t_TransportPublicKey & t_TransportSecretKey) =
    (TransportPublicKey tpk <: t_TransportPublicKey),
    (TransportSecretKey tsk <: t_TransportSecretKey)
    <:
    (t_TransportPublicKey & t_TransportSecretKey)
  in
  rng, hax_temp_output <: (v_R & (t_TransportPublicKey & t_TransportSecretKey))

/// Produce encrypted key share for given identity and transport key.
/// **Paper**: Section 5.3, protocol pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, encsign, m, tpk), S_i computes sigma_i = H(m)^{sk_i},
///  encrypts sigma_i as (C1, C2, C3) = (g1^t, g2^t, tpk_1^t * sigma_i),
///  and sends es_i = (C1, C2, C3) to a combiner."
/// Steps (adapted to our G2-sig convention):
///   1. `sigma_i = H(id)^{sk_i}` -- partial BLS signature (G2)
///   2. Choose random `r <- Z_q`
///   3. `C1 = g1^r` -- ElGamal randomness (G1)
///   4. `C2 = g2^r` -- ElGamal randomness (G2, for pairing verification)
///   5. `C3 = tpk^r * sigma_i` -- encrypted partial sig (G2)
/// **Security**: Theorem 6 (p.25) proves this realizes F_vetbls^{cEG2}
/// under co-CDH hardness. The leakage (co-ElGamal encryption of sigma_i)
/// is shown harmless for IBE by Theorem 7 (p.32).
let encrypt_key_share
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng v_R)
      (share: Golden_dkg.Threshold.Types.t_KeyShare)
      (identity: t_Slice u8)
      (tpk: t_TransportPublicKey)
      (rng: v_R)
    : (v_R & t_EncryptedKeyShare) =
  let h:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_identity_to_g2 identity
  in
  let sigma_i:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          h
          share.Golden_dkg.Threshold.Types.f_secret
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  let
  (tmp0: v_R),
  (out:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Ark_std.Rand_helper.f_rand #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      #v_R
      rng
  in
  let rng:v_R = tmp0 in
  let r:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    out
  in
  let c1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
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
          r
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let c2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G2.t_Config)
              #FStar.Tactics.Typeclasses.solve
              ()
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          r
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  let c3:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              tpk._0
              r
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
          (Core_models.Convert.f_from #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
              #FStar.Tactics.Typeclasses.solve
              sigma_i
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  let hax_temp_output:t_EncryptedKeyShare =
    { f_c1 = c1; f_c2 = c2; f_c3 = c3; f_signer = share.Golden_dkg.Threshold.Types.f_id }
    <:
    t_EncryptedKeyShare
  in
  rng, hax_temp_output <: (v_R & t_EncryptedKeyShare)

/// Verify encrypted key share via pairing equations.
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When a combiner receives this message, it checks that
///  e(C1, g2) = e(g1, C2) and that
///  e(C3, g2) = e(tpk, C2) * e(H(m), pk_i)"
/// Adapted to our convention (pk in G1, sig in G2):
///   Check 1: `e(C1, g2) = e(g1, C2)` -- G1/G2 randomness components are consistent
///   Check 2: `e(pk_i, H(id)) + e(C1, tpk) = e(g1, C3)` -- encryption is correct
/// This verification reveals NOTHING about sigma_i to the verifier.
/// The verifier only sees the encrypted form. (Paper Section 5.1, p.23:
/// "the encrypted signature shares actually do leak some information about
/// the signature share, namely, a verifiable ElGamal encryption of it.")
/// **NCC Audit**: Finding D7X (p.14) notes that identity checks on curve
/// points are important. Our pairing checks implicitly reject identity elements.
let verify_encrypted_key_share
      (eks: t_EncryptedKeyShare)
      (identity: t_Slice u8)
      (tpk: t_TransportPublicKey)
      (pk_share: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : bool =
  let g1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let g2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let h:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_identity_to_g2 identity
  in
  if
    (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
        eks.f_c1
        g2
      <:
      Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)) <>.
    (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
        g1
        eks.f_c2
      <:
      Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
  then false
  else
    let lhs:Ark_ec.Pairing.t_PairingOutput
    (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
      Core_models.Ops.Arith.f_add #(Ark_ec.Pairing.t_PairingOutput
          (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
        #(Ark_ec.Pairing.t_PairingOutput
          (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
        #FStar.Tactics.Typeclasses.solve
        (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
            #FStar.Tactics.Typeclasses.solve
            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
            pk_share
            h
          <:
          Ark_ec.Pairing.t_PairingOutput
          (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
        (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
            #FStar.Tactics.Typeclasses.solve
            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
            eks.f_c1
            tpk._0
          <:
          Ark_ec.Pairing.t_PairingOutput
          (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
    in
    let rhs:Ark_ec.Pairing.t_PairingOutput
    (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
      Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
        g1
        eks.f_c3
    in
    lhs =. rhs

/// Combine encrypted key shares via Lagrange interpolation in the exponent.
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When it received t valid such es_i = (C_{i,1}, C_{i,2}, C_{i,3})
///  from different servers S_i, i in S, it computes
///  es = (C1, C2, C3) = (prod_{i in S} C_{i,1}^{Lambda_{i,S}(0)}, ...)"
/// Uses standard Lagrange basis polynomial evaluation at 0:
///   Lambda_{i,S}(0) = prod_{j in S, j != i} (x_j / (x_j - x_i))
/// where x_i are the Shamir evaluation points (node IDs).
/// **Paper**: Section 4.1, p.10: "sk = sum_{i in S} Lambda_{i,S}(0) * sk_i"
/// The same interpolation applies in the exponent to the encrypted shares.
/// **NCC Audit**: Finding XD6 (p.6-8) warns about duplicate share handling.
/// We take the first `threshold` shares, assuming distinct signers.
let combine_encrypted_shares (shares: t_Slice t_EncryptedKeyShare) (threshold: usize)
    : t_EncryptedVetKey =
  let shares:t_Slice t_EncryptedKeyShare =
    if (Core_models.Slice.impl__len #t_EncryptedKeyShare shares <: usize) >. threshold
    then
      shares.[ { Core_models.Ops.Range.f_end = threshold } <: Core_models.Ops.Range.t_RangeTo usize
      ]
    else shares
  in
  let (ids: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter t_EncryptedKeyShare) (t_EncryptedKeyShare -> u32))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter t_EncryptedKeyShare)
          #FStar.Tactics.Typeclasses.solve
          #u32
          #(t_EncryptedKeyShare -> u32)
          (Core_models.Slice.impl__iter #t_EncryptedKeyShare shares
            <:
            Core_models.Slice.Iter.t_Iter t_EncryptedKeyShare)
          (fun s ->
              let s:t_EncryptedKeyShare = s in
              s.f_signer)
        <:
        Core_models.Iter.Adapters.Map.t_Map (Core_models.Slice.Iter.t_Iter t_EncryptedKeyShare)
          (t_EncryptedKeyShare -> u32))
  in
  let c1:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let c2:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let c3:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let
  (c1: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
  (c2: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config),
  (c3: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            t_EncryptedKeyShare)
          #FStar.Tactics.Typeclasses.solve
          shares
        <:
        Core_models.Slice.Iter.t_Iter t_EncryptedKeyShare)
      (c1, c2, c3
        <:
        (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
          Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config &
          Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config))
      (fun temp_0_ s ->
          let
          (c1: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
          (c2: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config),
          (c3: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
          =
            temp_0_
          in
          let s:t_EncryptedKeyShare = s in
          let li:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Golden_dkg.Threshold.Signing.lagrange_coeff s.f_signer
              (Alloc.Vec.impl_1__as_slice ids <: t_Slice u32)
          in
          let c1:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G1.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              c1
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  s.f_c1
                  li
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
          in
          let c2:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              c2
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G2.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  s.f_c2
                  li
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
          in
          let c3:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              c3
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G2.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  s.f_c3
                  li
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
          in
          c1, c2, c3
          <:
          (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config &
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config))
  in
  {
    f_c1
    =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      c1;
    f_c2
    =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      c2;
    f_c3
    =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      c3
  }
  <:
  t_EncryptedVetKey

/// Verify combined encrypted vetKey via pairing equation.
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When S_i receives es, it verifies that
///  e(C2, g2) = e(C1, tpk_2) * e(H(m), pk)"
/// Adapted to our convention:
///   `e(group_pk, H(id)) + e(C1, tpk) = e(g1, C3)`
/// This is the aggregated version of the per-share check. If this passes,
/// the encrypted vetKey is guaranteed to decrypt to a valid BLS signature.
let verify_encrypted_vetkey
      (evk: t_EncryptedVetKey)
      (identity: t_Slice u8)
      (tpk: t_TransportPublicKey)
      (group_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : bool =
  let g1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let h:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_identity_to_g2 identity
  in
  let lhs:Ark_ec.Pairing.t_PairingOutput
  (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
    Core_models.Ops.Arith.f_add #(Ark_ec.Pairing.t_PairingOutput
        (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
      #(Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
      #FStar.Tactics.Typeclasses.solve
      (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
          #FStar.Tactics.Typeclasses.solve
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          group_pk
          h
        <:
        Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
      (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
          #FStar.Tactics.Typeclasses.solve
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          evk.f_c1
          tpk._0
        <:
        Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
  in
  let rhs:Ark_ec.Pairing.t_PairingOutput
  (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
    Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      g1
      evk.f_c3
  in
  lhs =. rhs

/// Decrypt encrypted vetKey using transport secret key.
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, decrypt, pk', m, tpk, es), U parses es as (C1, C2, C3)
///  and looks up tsk from its local state. It decrypts
///  sigma = C3 * C1^{-tsk} and checks whether e(sigma, g2) = e(H(m), pk')."
/// Adapted to our convention (C2 in G2, C3 in G2):
///   sigma = C3 - C2 * tsk
///         = (tpk^r * H(id)^sk) - (g2^r * tsk)
///         = (g2^{tsk*r} * H(id)^sk) - (g2^{r*tsk})
///         = H(id)^sk    -- the vetKey!
/// Verification: `e(group_pk, H(id)) = e(g1, sigma)`
/// This is the standard BLS verification equation applied to the identity.
/// Returns `None` if decrypted value fails BLS verification (tampered ciphertext
/// or wrong transport key).
let decrypt_vetkey
      (evk: t_EncryptedVetKey)
      (tsk: t_TransportSecretKey)
      (identity: t_Slice u8)
      (group_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Core_models.Option.t_Option t_VetKey =
  let sigma:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_sub #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Convert.f_from #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
              #FStar.Tactics.Typeclasses.solve
              evk.f_c3
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
          (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              evk.f_c2
              tsk._0
            <:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  let g1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let h:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_identity_to_g2 identity
  in
  if
    (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
        group_pk
        h
      <:
      Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)) =.
    (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
        g1
        sigma
      <:
      Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))
  then
    Core_models.Option.Option_Some (VetKey sigma <: t_VetKey)
    <:
    Core_models.Option.t_Option t_VetKey
  else Core_models.Option.Option_None <: Core_models.Option.t_Option t_VetKey

/// Encrypt a message to an identity using Boneh-Franklin IBE.
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, encrypt, mpk', id, m), P checks that m in {0,1}^l.
///  It calls (sid_vetbls, hash, id) on F_vetbls to obtain response h.
///  It then chooses s <- {0,1}^kappa, sets t = H3(s, m), and computes
///  C = (g2^t, s XOR H2(e(h, mpk')^t), m XOR H4(s))"
/// **Key property**: Anyone can encrypt using ONLY the group public key and
/// the recipient's identity. No interaction with the network is needed.
/// The recipient can be offline. This is the defining feature of IBE.
/// **Original paper**: Boneh & Franklin [BF01], "Identity-Based Encryption
/// from the Weil Pairing", CRYPTO 2001. The FullIdent scheme uses the
/// Fujisaki-Okamoto transform (H3, H4) to achieve CCA security from
/// a CPA-secure BasicIdent scheme.
/// **Security**: Theorem 7 (p.32): pi_vetibe realizes F_vetibe under
/// co-BDH hardness in the random oracle model for H2, H3, H4.
/// Steps (adapted to our G1-pk convention):
///   1. Choose random seed `s <- {0,1}^256`
///   2. `t = H3(s, message)` -- FO derandomization
///   3. `u = g1^t` -- randomness point (G1; paper has g2^t)
///   4. `v = s XOR H2(e(mpk * t, H(id)))` -- encrypted seed
///   5. `w = message XOR H4(s)` -- encrypted message
let ibe_encrypt
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng v_R)
      (group_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (identity message: t_Slice u8)
      (rng: v_R)
    : (v_R & t_IBECiphertext) =
  let h:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_identity_to_g2 identity
  in
  let seed:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let (tmp0: v_R), (tmp1: t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #v_R #FStar.Tactics.Typeclasses.solve rng seed
  in
  let rng:v_R = tmp0 in
  let seed:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let t:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    hash_h3 seed message
  in
  let u:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
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
          t
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let mpk_t:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          group_pk
          t
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let pairing_val:Ark_ec.Pairing.t_PairingOutput
  (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
    Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      mpk_t
      h
  in
  let h2_mask:t_Array u8 (mk_usize 32) = hash_h2 pairing_val.Ark_ec.Pairing._0 in
  let v:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    xor_bytes (seed <: t_Slice u8) (h2_mask <: t_Slice u8)
  in
  let h4_mask:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    hash_h4 seed (Core_models.Slice.impl__len #u8 message <: usize)
  in
  let w:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    xor_bytes message (Alloc.Vec.impl_1__as_slice h4_mask <: t_Slice u8)
  in
  let hax_temp_output:t_IBECiphertext = { f_u = u; f_v = v; f_w = w } <: t_IBECiphertext in
  rng, hax_temp_output <: (v_R & t_IBECiphertext)

/// Decrypt IBE ciphertext using vetKey (BLS signature on the identity).
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, decrypt, id, C), user U checks whether it has a record (id, K)
///  in its state. If not, it ignores this input. Otherwise, it parses
///  C = (C1, C2, C3), computes s = C2 XOR H2(e(K, C1)), and recovers
///  m = C3 XOR H4(s). It also computes t = H3(s, m) and checks whether
///  C1 = g2^t."
/// Steps (adapted to our convention where u is in G1 and vetkey is in G2):
///   1. Compute `e(u, vetkey) = e(g1^t, H(id)^sk) = e(g1, H(id))^{t*sk}`
///   2. Recover seed: `s = v XOR H2(pairing_value)`
///   3. Recover message: `m = w XOR H4(s)`
///   4. **CCA check**: recompute `t = H3(s, m)` and verify `u == g1^t`
/// The CCA check (step 4) is the Fujisaki-Okamoto verification that rejects
/// maliciously modified ciphertexts. Without it, the scheme would only be
/// CPA-secure (BasicIdent). With it, the scheme is CCA-secure (FullIdent).
/// Returns `None` if:
///   - Seed length mismatch (v is not 32 bytes)
///   - CCA check fails (ciphertext was tampered with)
///   - Wrong vetKey (identity mismatch -- pairing produces wrong mask)
let ibe_decrypt (vetkey: t_VetKey) (ct: t_IBECiphertext)
    : Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  let pairing_val:Ark_ec.Pairing.t_PairingOutput
  (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config) =
    Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      ct.f_u
      vetkey._0
  in
  let h2_mask:t_Array u8 (mk_usize 32) = hash_h2 pairing_val.Ark_ec.Pairing._0 in
  if (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global ct.f_v <: usize) <>. mk_usize 32
  then
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  else
    let seed_vec:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      xor_bytes (Alloc.Vec.impl_1__as_slice ct.f_v <: t_Slice u8) (h2_mask <: t_Slice u8)
    in
    let seed:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
    let seed:t_Array u8 (mk_usize 32) =
      Core_models.Slice.impl__copy_from_slice #u8
        seed
        (Alloc.Vec.impl_1__as_slice seed_vec <: t_Slice u8)
    in
    let h4_mask:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      hash_h4 seed (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global ct.f_w <: usize)
    in
    let message:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      xor_bytes (Alloc.Vec.impl_1__as_slice ct.f_w <: t_Slice u8)
        (Alloc.Vec.impl_1__as_slice h4_mask <: t_Slice u8)
    in
    let t:Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
      hash_h3 seed (Alloc.Vec.impl_1__as_slice message <: t_Slice u8)
    in
    let expected_u:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
    =
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
            t
          <:
          Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
    in
    if expected_u <>. ct.f_u
    then
      Core_models.Option.Option_None
      <:
      Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    else
      Core_models.Option.Option_Some message
      <:
      Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
