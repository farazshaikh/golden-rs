module Golden_dkg.Bundle
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
  let open Ark_std.Rand_helper in
  let open Rand.Distributions.Distribution in
  let open Rand.Rng in
  ()

/// A Schnorr proof of knowledge of discrete log: proves knowledge of `sk` such
/// that `PK = g^sk`.
/// Per Appendix F of the Golden paper (IACR 2025/1924), this proof is required
/// when registering an identity public key with the PKI functionality `F_pki`.
/// The proof consists of a commitment `R = g^nonce` and a response
/// `s = nonce + challenge * sk` using the Fiat-Shamir heuristic.
/// Generate with [`prove`], verify with [`verify`]. The proof is bound to a
/// specific public key via the Fiat-Shamir challenge -- it cannot be reused for
/// a different key.
type t_SchnorrPoK = {
  f_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_response:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl: Core_models.Clone.t_Clone t_SchnorrPoK =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Fmt.t_Debug t_SchnorrPoK

unfold
let impl_1 = impl_1'

/// Fiat-Shamir challenge: c = H(g || pk || R) mod r.
/// Excluded from hax extraction (uses serialize_compressed with &mut).
/// Modeled as an opaque Random Oracle mapping in F*.
assume val compute_challenge
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (commitment: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)

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

/// Session identifier for replay protection.
/// A random 32-byte nonce generated per DKG/refresh/reshare session.
/// All participants in a session must use the same `SessionId`.
/// Messages with mismatched session IDs are rejected.
type t_SessionId = | SessionId : t_Array u8 (mk_usize 32) -> t_SessionId

let impl_4: Core_models.Clone.t_Clone t_SessionId =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Marker.t_Copy t_SessionId

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Fmt.t_Debug t_SessionId

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Marker.t_StructuralPartialEq t_SessionId

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Cmp.t_PartialEq t_SessionId t_SessionId

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Cmp.t_Eq t_SessionId

unfold
let impl_9 = impl_9'

/// Generate a random session ID.
let impl__random
      (#iimpl_59791891_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_59791891_)
      (rng: iimpl_59791891_)
    : (iimpl_59791891_ & t_SessionId) =
  let bytes:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let (tmp0: iimpl_59791891_), (tmp1: t_Slice u8) =
    Rand.Rng.f_fill #iimpl_59791891_
      #FStar.Tactics.Typeclasses.solve
      #(t_Slice u8)
      rng
      (bytes.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ] <: t_Slice u8)
  in
  let rng:iimpl_59791891_ = tmp0 in
  let bytes:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full bytes
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      tmp1
  in
  let _:Prims.unit = () in
  let hax_temp_output:t_SessionId = SessionId bytes <: t_SessionId in
  rng, hax_temp_output <: (iimpl_59791891_ & t_SessionId)

/// A scalar value that is zeroed from memory on drop.
/// SECURITY: Wraps `Fr` (BLS12-381 scalar field) for secret keys,
/// polynomial coefficients, and other sensitive values. The internal
/// representation is overwritten with zeros when the value goes out of scope.
type t_SecretScalar =
  | SecretScalar :
      Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
    -> t_SecretScalar

/// Create a new secret scalar.
let impl_1__new
      (v_val:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_SecretScalar = SecretScalar v_val <: t_SecretScalar

/// Get the inner scalar value.
let impl_1__inner (self: t_SecretScalar)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) = self._0

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
  let nonce:t_SecretScalar = impl_1__new out in
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
          (impl_1__inner nonce
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
      (impl_1__inner nonce
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Ops.Deref.t_Deref t_SecretScalar =
  {
    f_Target
    =
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4);
    f_deref_pre = (fun (self: t_SecretScalar) -> true);
    f_deref_post
    =
    (fun
        (self: t_SecretScalar)
        (out:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        ->
        true);
    f_deref = fun (self: t_SecretScalar) -> self._0
  }

/// A single encrypted share from node i to node j.
/// Per Round 0 line 7 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "sigma_{i,j} = (R_{i,j}, z_{i,j})"
/// where `R_{i,j} = g^{r_{i,j}}` is the eVRF pad commitment and
/// `z_{i,j} = r_{i,j} + x_bar_{i,j}` is the encrypted Shamir share.
type t_Ciphertext = {
  f_r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_encrypted_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl_11: Core_models.Clone.t_Clone t_Ciphertext =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Fmt.t_Debug t_Ciphertext

unfold
let impl_12 = impl_12'

/// Common fields shared between [`Round0Msg`] and [`ReshareMsg`].
/// Factored into a sub-struct so that hax generates unambiguous F* field paths
/// (`msg.dkg_header.ciphertexts` instead of `msg.ciphertexts`). Without this, F*'s
/// record type resolution confuses `t_Round0Msg` and `t_ReshareMsg` when both
/// are in scope, because they share identically-named fields.
type t_MessageHeader = {
  f_session_id:t_SessionId;
  f_from:u32;
  f_random_msg:t_Array u8 (mk_usize 32);
  f_vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global;
  f_ciphertexts:Std.Collections.Hash.Map.t_HashMap u32 t_Ciphertext Std.Hash.Random.t_RandomState
}

let impl_13: Core_models.Clone.t_Clone t_MessageHeader =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Fmt.t_Debug t_MessageHeader

unfold
let impl_14 = impl_14'

/// Round 0 broadcast message from a single node.
/// Per Round 0 lines 9-10 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "bmsg_i = {(msg_i, C_bar_i, sigma_{i,j}, pi_{i,j})} for j != i"
/// Contains the VSS commitment, encrypted shares for all peers, and eVRF proofs
/// demonstrating correct pad derivation.
type t_Round0Msg = {
  f_dkg_header:t_MessageHeader;
  f_evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
    Golden_dkg.Zk_evrf.t_EVRFProof
    Std.Hash.Random.t_RandomState;
  f_batch_evrf_proof:Core_models.Option.t_Option Golden_dkg.Zk_evrf.t_EVRFProof
}

let impl_15: Core_models.Clone.t_Clone t_Round0Msg =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Fmt.t_Debug t_Round0Msg

unfold
let impl_16 = impl_16'

/// Reshare broadcast message from an old-group member to the new group.
/// Sent by each old-group member during the [`crate::reshare`] protocol.
/// Structurally similar to [`Round0Msg`] but without eVRF proofs -- the reshare
/// protocol relies on VSS commitment verification against known public key shares
/// instead (see [`crate::reshare::verify_dealing`]).
/// The old member re-shares their secret key share `sk_i` using a fresh
/// degree-(t'-1) polynomial `g_i(x)` where `g_i(0) = sk_i`. The VSS commitment
/// allows verifiers to check `commitment[0] == PK_i` (the known public key share).
type t_ReshareMsg = { f_reshare_header:t_MessageHeader }

let impl_17: Core_models.Clone.t_Clone t_ReshareMsg =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': Core_models.Fmt.t_Debug t_ReshareMsg

unfold
let impl_18 = impl_18'

/// Output of the DKG protocol for a single node.
/// Per Round 1 line 17 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "return (PK, {PK_j}, sk_i)"
/// Contains the shared public key, per-participant public key shares, and
/// this node's secret key share.
type t_DkgOutput = {
  f_public_key:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Std.Hash.Random.t_RandomState;
  f_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl_19: Core_models.Clone.t_Clone t_DkgOutput =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20': Core_models.Fmt.t_Debug t_DkgOutput

unfold
let impl_20 = impl_20'

/// A participant's identity for the DKG protocol.
/// Each participant generates a `Participant` once (via [`Participant::new`]) and
/// retains it across DKG, refresh, and reshare sessions. The identity keypair
/// `(sk, pk)` is used for eVRF pad derivation (DH key exchange), and the Schnorr
/// proof of knowledge `pok` is required for PKI registration (Appendix F of the
/// Golden paper) to prevent rogue-key attacks.
/// # Example
/// ```rust,no_run
/// # use golden_dkg::types::Participant;
/// let mut rng = rand::rngs::OsRng;
/// let alice = Participant::new(1, &mut rng);
/// // alice.pk is the public key to share with other participants
/// // alice.pok should be verified by other participants on registration
/// ```
type t_Participant = {
  f_id:u32;
  f_sk:t_SecretScalar;
  f_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_pok:t_SchnorrPoK
}

/// Generate a new participant with a fresh identity keypair and Schnorr PoK.
/// Samples a random secret key `sk <- Z_p`, computes `pk = g^sk`, and
/// generates a Schnorr proof of knowledge. The caller should distribute
/// `pk` and `pok` to all other participants for PKI registration.
let impl_3__new
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (id: u32)
      (rng: iimpl_1039969868_)
    : (iimpl_1039969868_ & t_Participant) =
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
  let sk_val:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    out
  in
  let pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
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
          sk_val
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let (tmp0: iimpl_1039969868_), (out: t_SchnorrPoK) = prove #iimpl_1039969868_ sk_val pk rng in
  let rng:iimpl_1039969868_ = tmp0 in
  let pok:t_SchnorrPoK = out in
  let hax_temp_output:t_Participant =
    { f_id = id; f_sk = impl_1__new sk_val; f_pk = pk; f_pok = pok } <: t_Participant
  in
  rng, hax_temp_output <: (iimpl_1039969868_ & t_Participant)

/// Configuration for a DKG or refresh session.
/// All participants in a session must agree on the same configuration values.
/// Mismatched configurations will cause verification failures.
/// # Choosing `n` and `t`
/// - `n` -- total number of participants in the group
/// - `t` -- minimum number of shares required to reconstruct the secret (threshold).
///   The Shamir polynomial has degree `t - 1`, so any `t` shares suffice for
///   reconstruction and `t - 1` shares reveal nothing.
/// Common choices: `(n=3, t=2)` for 2-of-3, `(n=5, t=3)` for 3-of-5.
type t_DkgConfig = {
  f_n:u32;
  f_t:u32;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_session_id:t_SessionId
}

/// Output of Round 0: the broadcast message and private local state.
/// Returned by [`crate::dkg::create_dealing`] and [`crate::refresh::create_dealing`].
/// The `message` field should be broadcast to all peers. The `private_share` field
/// **must be kept secret** -- it is this participant's own Shamir share `x_bar_{i,i} = f_i(i)`
/// (or the delta share in the refresh case).
/// Both `private_share` and `own_vss_commitment` are needed by
/// [`crate::dkg::complete`] / [`crate::refresh::complete`] and should be retained
/// until the protocol completes.
type t_DkgDealing = {
  f_message:t_Round0Msg;
  f_private_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_own_vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global
}
