module Golden_dkg.Dkg
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
  let open Std.Hash.Random in
  ()

/// Generate a DKG dealing (Round 0 of Figure 4 in the Golden paper).
/// Each participant calls this once per session. The function:
/// 1. Samples a random secret contribution `omega_i`
/// 2. Creates a degree-(t-1) Shamir polynomial with `omega_i` as the constant term
/// 3. Encrypts each peer's share using an eVRF-derived pad from a DH shared secret
/// 4. Generates a batched eVRF proof covering all encrypted shares
/// # Parameters
/// - `participant` -- the caller's identity (keypair + ID)
/// - `config` -- session parameters (n, t, beta, session_id)
/// - `peers` -- map of **all** participant IDs to their identity public keys
///   (including the caller themselves)
/// - `rng` -- cryptographic random number generator
/// # Returns
/// A [`DkgDealing`] containing:
/// - `message` -- the [`Round0Msg`] to **broadcast** to all peers
/// - `private_share` -- the caller's own Shamir share (`x_bar_{i,i} = f_i(i)`),
///   which **must be kept secret** and passed to [`complete`]
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
    Golden_dkg.Protocol.round0 #iimpl_1039969868_
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
  (own_share:
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
          msg.Golden_dkg.Types.f_vss_commitment;
        Golden_dkg.Types.f_message = msg;
        Golden_dkg.Types.f_private_share = own_share
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

/// Verify a dealing received from another participant.
/// This is the **public verifiability** check from Round 1 (Figure 4, lines 5-9)
/// of the Golden paper. It can be performed by any party (including observers
/// who are not participants) using only public information.
/// # Checks performed
/// 1. **Session ID** -- the dealing's session ID matches the expected `config.session_id`
/// 2. **Ciphertext consistency** -- for each recipient `k`:
///    `g^{z_{j,k}} == R_{j,k} * X_bar_{j,k}` where `X_bar_{j,k}` is the
///    Feldman VSS share commitment (Figure 4, line 9)
/// 3. **eVRF proof** -- the batched eVRF proof (if present) verifies that all
///    pads were correctly derived from DH shared secrets (Figure 4, line 7)
/// # Parameters
/// - `dealing` -- the [`Round0Msg`] received from the sender
/// - `peers` -- the same peer map used in [`create_dealing`] (all participant PKs)
/// - `config` -- session parameters
/// # Errors
/// - [`DkgError::SessionMismatch`] -- dealing has a different session ID (possible replay)
/// - [`DkgError::CiphertextVerificationFailed`] -- a ciphertext is inconsistent
///   with the VSS commitment (sender is malicious or message was corrupted)
/// - [`DkgError::ProofError`] -- the eVRF proof failed verification
let verify_dealing
      (dealing: Golden_dkg.Types.t_Round0Msg)
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (config: Golden_dkg.Types.t_DkgConfig)
    : Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError =
  if dealing.Golden_dkg.Types.f_session_id <>. config.Golden_dkg.Types.f_session_id
  then
    Core_models.Result.Result_Err
    (Golden_dkg.Error.DkgError_SessionMismatch
      ({ Golden_dkg.Error.f_sender = dealing.Golden_dkg.Types.f_from })
      <:
      Golden_dkg.Error.t_DkgError)
    <:
    Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError
  else
    match
      Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                u32 Golden_dkg.Types.t_Ciphertext Std.Hash.Random.t_RandomState)
            #FStar.Tactics.Typeclasses.solve
            dealing.Golden_dkg.Types.f_ciphertexts
          <:
          Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
        ()
        (fun temp_0_ temp_1_ ->
            let _:Prims.unit = temp_0_ in
            let (recipient_id: u32), (ct: Golden_dkg.Types.t_Ciphertext) = temp_1_ in
            let expected:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config =
              Golden_dkg.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice dealing
                      .Golden_dkg.Types.f_vss_commitment
                  <:
                  t_Slice
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
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
                        Golden_dkg.Error.f_sender = dealing.Golden_dkg.Types.f_from;
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
      match
        Core_models.Option.impl__ok_or_else #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #Golden_dkg.Error.t_DkgError
          #(Prims.unit -> Golden_dkg.Error.t_DkgError)
          (Core_models.Option.impl_2__copied #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              (Std.Collections.Hash.Map.impl_2__get #u32
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #Std.Hash.Random.t_RandomState
                  #u32
                  peers
                  dealing.Golden_dkg.Types.f_from
                <:
                Core_models.Option.t_Option
                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
            <:
            Core_models.Option.t_Option
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              let args:u32 = dealing.Golden_dkg.Types.f_from <: u32 in
              let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                let list = [Core_models.Fmt.Rt.impl__new_display #u32 args] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list
              in
              Golden_dkg.Error.DkgError_ProofError
              (Core_models.Hint.must_use #Alloc.String.t_String
                  (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                          (mk_usize 1)
                          (let list = ["unknown sender "] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                          args
                        <:
                        Core_models.Fmt.t_Arguments)
                    <:
                    Alloc.String.t_String))
              <:
              Golden_dkg.Error.t_DkgError)
        <:
        Core_models.Result.t_Result
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Golden_dkg.Error.t_DkgError
      with
      | Core_models.Result.Result_Ok sender_pk ->
        (match
            dealing.Golden_dkg.Types.f_batch_evrf_proof
            <:
            Core_models.Option.t_Option Golden_dkg.Zk_evrf.t_EVRFProof
          with
          | Core_models.Option.Option_Some batch_proof ->
            let
            (peers_for_verify:
              Alloc.Vec.t_Vec
                (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
              (u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Alloc.Alloc.t_Global =
              Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                    (Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext)
                    (u32
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)))
                #FStar.Tactics.Typeclasses.solve
                #(Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Keys u32
                        Golden_dkg.Types.t_Ciphertext)
                    #FStar.Tactics.Typeclasses.solve
                    #(u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                    #(u32
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                    (Std.Collections.Hash.Map.impl_1__keys #u32
                        #Golden_dkg.Types.t_Ciphertext
                        #Std.Hash.Random.t_RandomState
                        dealing.Golden_dkg.Types.f_ciphertexts
                      <:
                      Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext)
                    (fun pid ->
                        let pid:u32 = pid in
                        pid,
                        (peers.[ pid ]
                          <:
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        <:
                        (u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config))
                  <:
                  Core_models.Iter.Adapters.Map.t_Map
                    (Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext)
                    (u32
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)))
            in
            let
            (pad_commitments:
              Alloc.Vec.t_Vec
                (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
              (u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Alloc.Alloc.t_Global =
              Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                    (Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
                    ((u32 & Golden_dkg.Types.t_Ciphertext)
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)))
                #FStar.Tactics.Typeclasses.solve
                #(Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter u32
                        Golden_dkg.Types.t_Ciphertext)
                    #FStar.Tactics.Typeclasses.solve
                    #(u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                    #((u32 & Golden_dkg.Types.t_Ciphertext)
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                    (Std.Collections.Hash.Map.impl_1__iter #u32
                        #Golden_dkg.Types.t_Ciphertext
                        #Std.Hash.Random.t_RandomState
                        dealing.Golden_dkg.Types.f_ciphertexts
                      <:
                      Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
                    (fun temp_0_ ->
                        let (pid: u32), (ct: Golden_dkg.Types.t_Ciphertext) = temp_0_ in
                        pid, ct.Golden_dkg.Types.f_r_commitment
                        <:
                        (u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config))
                  <:
                  Core_models.Iter.Adapters.Map.t_Map
                    (Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
                    ((u32 & Golden_dkg.Types.t_Ciphertext)
                        -> (u32 &
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)))
            in
            (match
                Golden_dkg.Zk_evrf.verify_evrf_batch sender_pk
                  (Alloc.Vec.impl_1__as_slice peers_for_verify
                    <:
                    t_Slice
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
                  (Alloc.Vec.impl_1__as_slice pad_commitments
                    <:
                    t_Slice
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
                  config.Golden_dkg.Types.f_beta
                  batch_proof
                <:
                Core_models.Result.t_Result bool Alloc.String.t_String
              with
              | Core_models.Result.Result_Ok true ->
                Core_models.Result.Result_Ok (() <: Prims.unit)
                <:
                Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError
              | Core_models.Result.Result_Ok false ->
                let args:u32 = dealing.Golden_dkg.Types.f_from <: u32 in
                let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                  let list = [Core_models.Fmt.Rt.impl__new_display #u32 args] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list
                in
                Core_models.Result.Result_Err
                (Golden_dkg.Error.DkgError_ProofError
                  (Core_models.Hint.must_use #Alloc.String.t_String
                      (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                              (mk_usize 1)
                              (let list = ["batch eVRF verification failed for sender "] in
                                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                                Rust_primitives.Hax.array_of_list 1 list)
                              args
                            <:
                            Core_models.Fmt.t_Arguments)
                        <:
                        Alloc.String.t_String))
                  <:
                  Golden_dkg.Error.t_DkgError)
                <:
                Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError
              | Core_models.Result.Result_Err e ->
                Core_models.Result.Result_Err
                (Golden_dkg.Error.DkgError_ProofError e <: Golden_dkg.Error.t_DkgError)
                <:
                Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
          | _ ->
            Core_models.Result.Result_Ok (() <: Prims.unit)
            <:
            Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result Prims.unit Golden_dkg.Error.t_DkgError

/// Complete the DKG protocol (Round 1 of Figure 4: decryption + aggregation).
/// Decrypts each peer's encrypted share addressed to this participant by
/// re-deriving the eVRF pad from the DH shared secret (Figure 4, lines 10-12),
/// then aggregates all shares across dealers to produce the final secret key
/// share `sk_i = sum_j x_bar_{j,i}` and the shared public key
/// `PK = product_j A_{j,0}` (Figure 4, lines 13-17).
/// # Preconditions
/// - All peer dealings in `peer_dealings` **must** have been verified via
///   [`verify_dealing`] before calling this function. Passing unverified
///   dealings may produce incorrect or insecure output.
/// - `peers` must be the same peer map used in [`create_dealing`].
/// # Parameters
/// - `participant` -- the caller's identity
/// - `own_dealing` -- the caller's own [`DkgDealing`] from [`create_dealing`]
/// - `peer_dealings` -- verified [`Round0Msg`] messages from all other participants,
///   keyed by sender [`NodeId`]
/// - `peers` -- all participant IDs mapped to identity public keys
/// - `config` -- session parameters
/// # Returns
/// A [`DkgOutput`] containing:
/// - `public_key` -- the shared group public key `PK = g^sk`
/// - `public_key_shares` -- per-participant public key shares `PK_j = g^{sk_j}`
/// - `secret_share` -- this participant's secret key share `sk_i`
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
    : Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_DkgError =
  Golden_dkg.Protocol.round1 participant.Golden_dkg.Types.f_id
    (Golden_dkg.Types.impl_SecretScalar__inner participant.Golden_dkg.Types.f_sk
      <:
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    peers
    own_dealing.Golden_dkg.Types.f_private_share
    (Core_models.Clone.f_clone #(Alloc.Vec.t_Vec
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        own_dealing.Golden_dkg.Types.f_own_vss_commitment
      <:
      Alloc.Vec.t_Vec
        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        Alloc.Alloc.t_Global)
    peer_dealings
    config.Golden_dkg.Types.f_beta
    config.Golden_dkg.Types.f_session_id
