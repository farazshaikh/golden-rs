module Golden_dkg.Threshold.Beacon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G2 in
  let open Ark_ec in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_serialize in
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
  let open Std.Io in
  let open Std.Io.Impls in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// Compute the message digest for a given round.
/// - **Chained**: `SHA-256(prev_sig || round.to_be_bytes())`
/// - **Unchained** (prev_sig is `None`): `SHA-256(round.to_be_bytes())`
/// The big-endian encoding of the round number matches the drand specification.
let digest_message (round: u64) (prev_sig: Core_models.Option.t_Option (t_Slice u8))
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
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
    match prev_sig <: Core_models.Option.t_Option (t_Slice u8) with
    | Core_models.Option.Option_Some sig ->
      let hasher:Digest.Core_api.Wrapper.t_CoreWrapper
      (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
          (Typenum.Uint.t_UInt
              (Typenum.Uint.t_UInt
                  (Typenum.Uint.t_UInt
                      (Typenum.Uint.t_UInt
                          (Typenum.Uint.t_UInt
                              (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                              Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0
              ) Typenum.Bit.t_B0)
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
          sig
      in
      hasher
    | _ -> hasher
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
      #(t_Array u8 (mk_usize 8))
      hasher
      (Core_models.Num.impl_u64__to_be_bytes round <: t_Array u8 (mk_usize 8))
  in
  Alloc.Slice.impl__to_vec #u8
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

/// Hash an arbitrary byte digest to a BLS12-381 G2 curve point.
/// Uses SHA-256 → ChaCha8Rng → `G2Projective::rand` for deterministic
/// hash-to-curve.  This matches the approach used in the golden-dkg examples.
let hash_to_g2 (digest: t_Slice u8)
    : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
  let hash:Generic_array.t_GenericArray u8
    (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
        Typenum.Bit.t_B0) =
    Digest.Digest.f_digest #(Digest.Core_api.Wrapper.t_CoreWrapper
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
      digest
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

/// Derive 32 bytes of randomness from a threshold signature.
/// `randomness = SHA-256(signature_bytes)`
let derive_randomness (signature: t_Slice u8) : t_Array u8 (mk_usize 32) =
  let hash:Generic_array.t_GenericArray u8
    (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
        Typenum.Bit.t_B0) =
    Digest.Digest.f_digest #(Digest.Core_api.Wrapper.t_CoreWrapper
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
      signature
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
          hash
        <:
        t_Slice u8)
  in
  out

/// Serialize a G2 point to compressed bytes.
let g2_to_bytes
      (point: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(deref(point)), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "G2 serialize"
  in
  buf

/// Construct a new beacon from a round number and threshold signature.
/// For chained mode, `prev_sig` should be the previous round's signature
/// bytes.  For unchained mode, pass `None`.
let impl__new
      (round: u64)
      (prev_sig: Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      (threshold_sig: Golden_dkg.Threshold.Types.t_ThresholdSignature)
    : Golden_dkg.Threshold.Types.t_Beacon =
  let sig_bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    g2_to_bytes threshold_sig.Golden_dkg.Threshold.Types.f_signature
  in
  let randomness:t_Array u8 (mk_usize 32) =
    derive_randomness (Alloc.Vec.impl_1__as_slice sig_bytes <: t_Slice u8)
  in
  {
    Golden_dkg.Threshold.Types.f_round = round;
    Golden_dkg.Threshold.Types.f_previous_signature = prev_sig;
    Golden_dkg.Threshold.Types.f_signature = sig_bytes;
    Golden_dkg.Threshold.Types.f_randomness = randomness
  }
  <:
  Golden_dkg.Threshold.Types.t_Beacon

/// Verify this beacon's signature against the group public key.
/// Recomputes the message digest according to `mode`, hashes it to G2,
/// and checks the BLS pairing equation.
let impl__verify
      (self: Golden_dkg.Threshold.Types.t_Beacon)
      (group_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (mode: Golden_dkg.Threshold.Types.t_BeaconMode)
    : bool =
  let prev:Core_models.Option.t_Option (t_Slice u8) =
    match mode <: Golden_dkg.Threshold.Types.t_BeaconMode with
    | Golden_dkg.Threshold.Types.BeaconMode_Chained  ->
      Core_models.Option.impl__as_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        self.Golden_dkg.Threshold.Types.f_previous_signature
    | Golden_dkg.Threshold.Types.BeaconMode_Unchained  ->
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice u8)
  in
  let digest:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    digest_message self.Golden_dkg.Threshold.Types.f_round prev
  in
  let msg_hash:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    hash_to_g2 (Alloc.Vec.impl_1__as_slice digest <: t_Slice u8)
  in
  let (sig: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config):Ark_ec.Models.Short_weierstrass.Affine.t_Affine
  Ark_bls12_381_.Curves.G2.t_Config =
    Core_models.Result.impl__expect #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G2.t_Config)
      #Ark_serialize.Error.t_SerializationError
      (Ark_serialize.f_deserialize_compressed #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G2.t_Config)
          #FStar.Tactics.Typeclasses.solve
          #(t_Slice u8)
          (Alloc.Vec.impl_1__as_slice self.Golden_dkg.Threshold.Types.f_signature <: t_Slice u8)
        <:
        Core_models.Result.t_Result
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          Ark_serialize.Error.t_SerializationError)
      "deserialize G2 sig"
  in
  let threshold_sig:Golden_dkg.Threshold.Types.t_ThresholdSignature =
    { Golden_dkg.Threshold.Types.f_signature = sig }
    <:
    Golden_dkg.Threshold.Types.t_ThresholdSignature
  in
  Golden_dkg.Threshold.Signing.verify msg_hash threshold_sig group_pk
