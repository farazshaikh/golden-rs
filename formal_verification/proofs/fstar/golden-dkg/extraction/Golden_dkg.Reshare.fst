module Golden_dkg.Reshare
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Golden_dkg.Types in
  let open Rand.Rng in
  let open Std.Hash.Random in
  ()

/// Old member creates a reshare dealing for the new group.
/// The old member re-shares their existing secret key share `old_share` (= `sk_i`)
/// to the new group by creating a fresh degree-(t_new - 1) Shamir polynomial
/// `g_i(x)` with `g_i(0) = old_share`, then encrypting each new member's
/// sub-share using eVRF-derived pads.
/// # Parameters
/// - `old_participant` -- the old member's identity
/// - `old_share` -- the old member's secret key share `sk_i` from the previous DKG
/// - `new_members` -- map of new-group member IDs to their identity public keys
/// - `t_new` -- threshold for the new group
/// - `beta` -- public parameter for the leftover hash lemma
/// - `session_id` -- unique session identifier for this reshare
/// - `rng` -- cryptographic random number generator
/// # Returns
/// A [`ReshareMsg`] to broadcast to the new group.
/// # Errors
/// Returns [`ReshareError`] if message construction fails.
let create_dealing
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (old_participant: Golden_dkg.Types.t_Participant)
      (old_share:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (new_members:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (tt_new: u32)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (session_id: Golden_dkg.Types.t_SessionId)
      (rng: iimpl_1039969868_)
    : (iimpl_1039969868_ &
      Core_models.Result.t_Result Golden_dkg.Types.t_ReshareMsg Golden_dkg.Error.t_ReshareError) =
  let (tmp0: iimpl_1039969868_), (out: Golden_dkg.Types.t_ReshareMsg) =
    Golden_dkg.Reshare_protocol.reshare_deal #iimpl_1039969868_
      old_participant.Golden_dkg.Types.f_id
      old_share
      (Golden_dkg.Types.impl_SecretScalar__inner old_participant.Golden_dkg.Types.f_sk
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      new_members
      tt_new
      beta
      rng
      session_id
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let hax_temp_output:Core_models.Result.t_Result Golden_dkg.Types.t_ReshareMsg
    Golden_dkg.Error.t_ReshareError =
    Core_models.Result.Result_Ok out
    <:
    Core_models.Result.t_Result Golden_dkg.Types.t_ReshareMsg Golden_dkg.Error.t_ReshareError
  in
  rng, hax_temp_output
  <:
  (iimpl_1039969868_ &
    Core_models.Result.t_Result Golden_dkg.Types.t_ReshareMsg Golden_dkg.Error.t_ReshareError)

/// Verify a reshare dealing from an old-group member.
/// Checks that the dealing's first VSS commitment coefficient `A_{i,0}` matches
/// the old member's known public key share `PK_i = g^{sk_i}`. This ensures the
/// old member is re-sharing their actual secret share (not an arbitrary value).
/// # Parameters
/// - `dealing` -- the [`ReshareMsg`] received from an old-group member
/// - `old_pk_shares` -- public key shares from the old DKG output
///   (`DkgOutput::public_key_shares`), keyed by old-group [`NodeId`]
/// - `session_id` -- expected session identifier
/// # Errors
/// - [`ReshareError::SessionMismatch`] -- dealing has a different session ID
/// - [`ReshareError::CiphertextVerificationFailed`] -- `commitment[0]` does not
///   match the sender's known public key share (sender is dishonest or using
///   the wrong share)
let verify_dealing
      (dealing: Golden_dkg.Types.t_ReshareMsg)
      (old_pk_shares:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (session_id: Golden_dkg.Types.t_SessionId)
    : Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_ReshareError =
  if dealing.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_session_id <>. session_id
  then
    Core_models.Result.Result_Err
    (Golden_dkg.Error.ReshareError_SessionMismatch
      ({
          Golden_dkg.Error.f_sender
          =
          dealing.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_from
        })
      <:
      Golden_dkg.Error.t_ReshareError)
    <:
    Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_ReshareError
  else
    match
      Std.Collections.Hash.Map.impl_2__get #u32
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #Std.Hash.Random.t_RandomState
        #u32
        old_pk_shares
        dealing.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_from
      <:
      Core_models.Option.t_Option
      (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    with
    | Core_models.Option.Option_Some expected_pk_share ->
      if
        (dealing.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_vss_commitment.[ mk_usize 0 ]
          <:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) <>.
        expected_pk_share
      then
        Core_models.Result.Result_Err
        (Golden_dkg.Error.ReshareError_CiphertextVerificationFailed
          ({
              Golden_dkg.Error.f_sender
              =
              dealing.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_from;
              Golden_dkg.Error.f_recipient = mk_u32 0
            })
          <:
          Golden_dkg.Error.t_ReshareError)
        <:
        Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_ReshareError
      else
        Core_models.Result.Result_Ok (() <: Prims.unit)
        <:
        Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_ReshareError
    | _ ->
      Core_models.Result.Result_Ok (() <: Prims.unit)
      <:
      Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_ReshareError

/// New member completes resharing from verified old-group dealings.
/// The new member collects at least `t_old` verified [`ReshareMsg`] messages,
/// decrypts the sub-shares addressed to them, and performs Lagrange interpolation
/// to recover their new share of the global secret `sk`. The resulting
/// [`DkgOutput`] has the same `public_key` as the old group's output.
/// # Parameters
/// - `new_participant` -- the new member's identity
/// - `dealings` -- verified [`ReshareMsg`] messages from old-group members,
///   keyed by old-group sender [`NodeId`] (need at least `t_old` dealings)
/// - `old_members` -- map of old-group member IDs to their identity public keys
/// - `original_pk` -- the shared public key `PK` from the old group's DKG output
/// - `old_pk_shares` -- per-participant public key shares from the old DKG
/// - `t_old` -- the old group's threshold parameter
/// - `beta` -- public parameter for the leftover hash lemma
/// - `session_id` -- session identifier (must match the dealings)
/// # Returns
/// A [`DkgOutput`] with the new member's secret share of `sk` under the new
/// group's `(n', t')` parameters.
/// # Errors
/// - [`ReshareError::InsufficientDealers`] -- fewer than `t_old` dealings received
/// - [`ReshareError::MissingCiphertext`] -- a dealer didn't include this recipient
/// - [`ReshareError::NoMessages`] -- no dealings received at all
let complete
      (new_participant: Golden_dkg.Types.t_Participant)
      (dealings:
          Std.Collections.Hash.Map.t_HashMap u32
            Golden_dkg.Types.t_ReshareMsg
            Std.Hash.Random.t_RandomState)
      (old_members:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (original_pk:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (old_pk_shares:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (tt_old: u32)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (session_id: Golden_dkg.Types.t_SessionId)
    : Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_ReshareError =
  Golden_dkg.Reshare_protocol.reshare_receive new_participant.Golden_dkg.Types.f_id
    (Golden_dkg.Types.impl_SecretScalar__inner new_participant.Golden_dkg.Types.f_sk
      <:
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    old_members
    dealings
    beta
    original_pk
    old_pk_shares
    tt_old
    session_id
