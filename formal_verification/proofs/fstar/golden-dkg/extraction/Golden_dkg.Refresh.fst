module Golden_dkg.Refresh
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_ec in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Golden_dkg.Types in
  let open Rand.Rng in
  let open Std.Collections.Hash.Map in
  ()

/// Generate a refresh dealing (zero-secret sharing, Section 5.2).
/// Identical to [`crate::dkg::create_dealing`] except the secret contribution
/// `omega_i` is fixed to zero instead of being sampled randomly. The resulting
/// shares are "delta" values that will be added to existing shares during
/// [`complete`].
/// # Parameters
/// - `participant` -- the caller's identity (keypair + ID)
/// - `config` -- session parameters (n, t, beta, session_id); should use the
///   same `n` and `t` as the original DKG
/// - `peers` -- map of all participant IDs to identity public keys
/// - `rng` -- cryptographic random number generator
/// # Returns
/// A [`DkgDealing`] where `private_share` is the caller's own delta share
/// (`f_i(i)` with `f_i(0) = 0`).
/// # Errors
/// Returns [`DkgError`] if eVRF proof generation fails.
let create_dealing
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (participant: Golden_dkg.Types.t_Participant)
      (config: Golden_dkg.Types.t_DkgConfig)
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (rng: iimpl_1039969868_)
    : (iimpl_1039969868_ &
      Core_models.Result.t_Result Golden_dkg.Types.t_DkgDealing Golden_dkg.Error.t_DkgError) =
  let
  (tmp0: iimpl_1039969868_),
  (out:
    (Golden_dkg.Types.t_Round0Msg &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
    Golden_dkg.Protocol.round0_refresh #iimpl_1039969868_
      participant.Golden_dkg.Types.f_id
      config.Golden_dkg.Types.f_n
      config.Golden_dkg.Types.f_t
      (Golden_dkg.Types.impl_SecretScalar__inner participant.Golden_dkg.Types.f_sk
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      peers
      config.Golden_dkg.Types.f_beta
      rng
      config.Golden_dkg.Types.f_session_id
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let
  (msg: Golden_dkg.Types.t_Round0Msg),
  (own_delta:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    out
  in
  let hax_temp_output:Core_models.Result.t_Result Golden_dkg.Types.t_DkgDealing
    Golden_dkg.Error.t_DkgError =
    Core_models.Result.Result_Ok
    ({
        Golden_dkg.Types.f_own_vss_commitment
        =
        Core_models.Clone.f_clone #(Alloc.Vec.t_Vec
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          msg.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_vss_commitment;
        Golden_dkg.Types.f_message = msg;
        Golden_dkg.Types.f_private_share = own_delta
      }
      <:
      Golden_dkg.Types.t_DkgDealing)
    <:
    Core_models.Result.t_Result Golden_dkg.Types.t_DkgDealing Golden_dkg.Error.t_DkgError
  in
  rng, hax_temp_output
  <:
  (iimpl_1039969868_ &
    Core_models.Result.t_Result Golden_dkg.Types.t_DkgDealing Golden_dkg.Error.t_DkgError)

/// Verify a refresh dealing from another participant.
/// In addition to the standard ciphertext consistency checks (same as
/// [`crate::dkg::verify_dealing`]), this verifies the **zero-secret invariant**
/// from Section 5.2: the first VSS commitment coefficient `A_{j,0}` must be the
/// group identity element (`g^0`), ensuring `f_j(0) = 0`.
/// # Checks performed
/// 1. **Session ID** -- matches `config.session_id`
/// 2. **Zero-secret** -- `dealing.vss_commitment[0]` is the point at infinity
/// 3. **Ciphertext consistency** -- `g^{z_{j,k}} == R_{j,k} * X_bar_{j,k}`
///    for each recipient `k`
/// # Errors
/// - [`DkgError::SessionMismatch`] -- session ID mismatch (possible replay)
/// - [`DkgError::ZeroSecretViolation`] -- `A_{j,0}` is not the identity;
///   the sender is attempting to shift the global secret
/// - [`DkgError::CiphertextVerificationFailed`] -- ciphertext/VSS mismatch
let verify_dealing
      (dealing: Golden_dkg.Types.t_Round0Msg)
      (e_peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (config: Golden_dkg.Types.t_DkgConfig)
    : Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError =
  if
    dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_session_id <>.
    config.Golden_dkg.Types.f_session_id
  then
    Core_models.Result.Result_Err
    (Golden_dkg.Error.DkgError_SessionMismatch
      ({ Golden_dkg.Error.f_sender = dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_from }
      )
      <:
      Golden_dkg.Error.t_DkgError)
    <:
    Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError
  else
    if
      ~.(dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_vss_commitment.[ mk_usize 0 ]
        <:
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
    then
      Core_models.Result.Result_Err
      (Golden_dkg.Error.DkgError_ZeroSecretViolation
        ({
            Golden_dkg.Error.f_sender
            =
            dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_from
          })
        <:
        Golden_dkg.Error.t_DkgError)
      <:
      Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError
    else
      match
        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                  u32 Golden_dkg.Types.t_Ciphertext Std.Hash.Random.t_RandomState)
              #FStar.Tactics.Typeclasses.solve
              dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_ciphertexts
            <:
            Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
          ()
          (fun temp_0_ temp_1_ ->
              let _:Prims.unit = temp_0_ in
              let (recipient_id: u32), (ct: Golden_dkg.Types.t_Ciphertext) = temp_1_ in
              let expected:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
              Ark_bls12_381_.Curves.G1.t_Config =
                Golden_dkg.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice dealing
                        .Golden_dkg.Types.f_dkg_header
                        .Golden_dkg.Types.f_vss_commitment
                    <:
                    t_Slice
                    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
                  recipient_id
              in
              let lhs:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
              Ark_bls12_381_.Curves.G1.t_Config =
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
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                      ct.Golden_dkg.Types.f_encrypted_share
                    <:
                    Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config)
              in
              let rhs:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
              Ark_bls12_381_.Curves.G1.t_Config =
                Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #FStar.Tactics.Typeclasses.solve
                  (Core_models.Ops.Arith.f_add #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config)
                      #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config)
                      #FStar.Tactics.Typeclasses.solve
                      (Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)
                          #FStar.Tactics.Typeclasses.solve
                          ct.Golden_dkg.Types.f_r_commitment
                        <:
                        Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config)
                      (Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)
                          #FStar.Tactics.Typeclasses.solve
                          expected
                        <:
                        Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config)
                    <:
                    Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config)
              in
              if lhs <>. rhs
              then
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err
                    (Golden_dkg.Error.DkgError_CiphertextVerificationFailed
                      ({
                          Golden_dkg.Error.f_sender
                          =
                          dealing.Golden_dkg.Types.f_dkg_header.Golden_dkg.Types.f_from;
                          Golden_dkg.Error.f_recipient = recipient_id
                        })
                      <:
                      Golden_dkg.Error.t_DkgError)
                    <:
                    Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
                    (Prims.unit & Prims.unit))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
                      (Prims.unit & Prims.unit)) Prims.unit
              else
                Core_models.Ops.Control_flow.ControlFlow_Continue ()
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
                      (Prims.unit & Prims.unit)) Prims.unit)
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError) Prims.unit
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
        Core_models.Result.Result_Ok (() <: Prims.unit)
        <:
        Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError

/// Complete the refresh protocol: apply zero-sharing deltas to existing shares.
/// Decrypts each peer's delta share, aggregates across all dealers, and adds
/// the result to the participant's existing secret key share:
/// `sk_i' = sk_i + sum_j delta_{j,i}`.
/// The public key `PK` is preserved (since `sum_j f_j(0) = 0`), but all
/// individual shares are rotated. Per-participant public key shares are
/// recomputed: `PK_j' = PK_j * g^{sum_k delta_{k,j}}`.
/// # Preconditions
/// - All peer dealings must have been verified via [`verify_dealing`].
/// - `existing_output` must be the [`DkgOutput`] from the most recent DKG or
///   refresh round for this group.
/// # Parameters
/// - `participant` -- the caller's identity
/// - `own_dealing` -- the caller's own [`DkgDealing`] from [`create_dealing`]
/// - `peer_dealings` -- verified refresh messages from all other participants
/// - `peers` -- all participant IDs mapped to identity public keys
/// - `config` -- session parameters
/// - `existing_output` -- the [`DkgOutput`] to refresh (shares will be rotated)
/// # Returns
/// A new [`DkgOutput`] with rotated shares but the same `public_key`.
/// # Errors
/// Returns [`DkgError`] if share decryption or aggregation fails.
let complete
      (participant: Golden_dkg.Types.t_Participant)
      (own_dealing: Golden_dkg.Types.t_DkgDealing)
      (peer_dealings:
          Std.Collections.Hash.Map.t_HashMap u32
            Golden_dkg.Types.t_Round0Msg
            Std.Hash.Random.t_RandomState)
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (config: Golden_dkg.Types.t_DkgConfig)
      (existing_output: Golden_dkg.Types.t_DkgOutput)
    : Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_DkgError =
  Golden_dkg.Protocol.round1_refresh participant.Golden_dkg.Types.f_id
    (Golden_dkg.Types.impl_SecretScalar__inner participant.Golden_dkg.Types.f_sk
      <:
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) peers
    own_dealing.Golden_dkg.Types.f_private_share
    (Core_models.Clone.f_clone #(Alloc.Vec.t_Vec
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        own_dealing.Golden_dkg.Types.f_own_vss_commitment
      <:
      Alloc.Vec.t_Vec
        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        Alloc.Alloc.t_Global) peer_dealings config.Golden_dkg.Types.f_beta
    existing_output.Golden_dkg.Types.f_secret_share existing_output.Golden_dkg.Types.f_public_key
    existing_output.Golden_dkg.Types.f_public_key_shares config.Golden_dkg.Types.f_session_id
