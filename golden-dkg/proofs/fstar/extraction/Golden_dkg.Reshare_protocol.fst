module Golden_dkg.Reshare_protocol
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
  let open Golden_dkg.Types in
  let open Rand.Rng in
  let open Std.Collections.Hash.Map in
  let open Std.Hash.Random in
  ()

/// Old node deals its existing share to the new group.
/// Creates a polynomial `g_i` of degree `(t_new - 1)` with `g_i(0) = old_share`,
/// encrypts `g_i(j)` for each new member `j` using eVRF pads. The VSS commitment
/// allows new members to verify that `g_i(0)` equals the dealer's known public
/// key share `g^{sk_i}`.
let reshare_deal
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (old_id: u32)
      (old_share old_sk_identity:
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
      (rng: iimpl_1039969868_)
      (session_id: Golden_dkg.Types.t_SessionId)
    : (iimpl_1039969868_ & Golden_dkg.Types.t_ReshareMsg) =
  let (tmp0: iimpl_1039969868_), (out: Golden_dkg.Shamir.t_Polynomial) =
    Golden_dkg.Shamir.impl_Polynomial__new_random #iimpl_1039969868_
      old_share
      (cast (tt_new -! mk_u32 1 <: u32) <: usize)
      rng
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let poly:Golden_dkg.Shamir.t_Polynomial = out in
  let vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Golden_dkg.Vss.commit poly
  in
  let random_msg:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let (tmp0: iimpl_1039969868_), (tmp1: t_Slice u8) =
    Rand.Rng.f_fill #iimpl_1039969868_
      #FStar.Tactics.Typeclasses.solve
      #(t_Slice u8)
      rng
      (random_msg.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
        <:
        t_Slice u8)
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let random_msg:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full random_msg
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      tmp1
  in
  let _:Prims.unit = () in
  let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
    Golden_dkg.Types.t_Ciphertext
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32 #Golden_dkg.Types.t_Ciphertext ()
  in
  let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
    Golden_dkg.Types.t_Ciphertext
    Std.Hash.Random.t_RandomState =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          new_members
        <:
        Std.Collections.Hash.Map.t_Iter u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      ciphertexts
      (fun ciphertexts temp_1_ ->
          let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
            Golden_dkg.Types.t_Ciphertext
            Std.Hash.Random.t_RandomState =
            ciphertexts
          in
          let
          (new_id: u32),
          (new_pk:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
            temp_1_
          in
          let share_for_new:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Golden_dkg.Shamir.impl_Polynomial__evaluate poly
              (Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #u64
                  #FStar.Tactics.Typeclasses.solve
                  (cast (new_id <: u32) <: u64)
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          in
          let
          (r_pad:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
          (r_commitment:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
            Golden_dkg.Evrf.derive_pad old_sk_identity new_pk (random_msg <: t_Slice u8) beta
          in
          let encrypted_share:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Ops.Arith.f_add #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              r_pad
              share_for_new
          in
          let
          (tmp0:
            Std.Collections.Hash.Map.t_HashMap u32
              Golden_dkg.Types.t_Ciphertext
              Std.Hash.Random.t_RandomState),
          (out: Core_models.Option.t_Option Golden_dkg.Types.t_Ciphertext) =
            Std.Collections.Hash.Map.impl_2__insert #u32
              #Golden_dkg.Types.t_Ciphertext
              #Std.Hash.Random.t_RandomState
              ciphertexts
              new_id
              ({
                  Golden_dkg.Types.f_r_commitment = r_commitment;
                  Golden_dkg.Types.f_encrypted_share = encrypted_share
                }
                <:
                Golden_dkg.Types.t_Ciphertext)
          in
          let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
            Golden_dkg.Types.t_Ciphertext
            Std.Hash.Random.t_RandomState =
            tmp0
          in
          let _:Core_models.Option.t_Option Golden_dkg.Types.t_Ciphertext = out in
          ciphertexts)
  in
  let hax_temp_output:Golden_dkg.Types.t_ReshareMsg =
    {
      Golden_dkg.Types.f_reshare_header
      =
      {
        Golden_dkg.Types.f_session_id = session_id;
        Golden_dkg.Types.f_from = old_id;
        Golden_dkg.Types.f_random_msg = random_msg;
        Golden_dkg.Types.f_vss_commitment = vss_commitment;
        Golden_dkg.Types.f_ciphertexts = ciphertexts
      }
      <:
      Golden_dkg.Types.t_MessageHeader
    }
    <:
    Golden_dkg.Types.t_ReshareMsg
  in
  rng, hax_temp_output <: (iimpl_1039969868_ & Golden_dkg.Types.t_ReshareMsg)

/// New node receives resharing messages from old group and computes new share.
/// Each old member `i` dealt their share `sk_i` under polynomial `g_i`.
/// New member `j` decrypts `g_i(j)` from each old member, then computes:
///   `new_sk_j = sum_{i in S} g_i(j) * L_i(0)`
/// where `S` is the set of old members used and `L_i(0)` are Lagrange coefficients
/// for the old members' indices. This reconstructs a valid Shamir share of the
/// original secret under the new group's polynomial structure.
let reshare_receive
      (new_id: u32)
      (new_sk_identity:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (old_members:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (received:
          Std.Collections.Hash.Map.t_HashMap u32
            Golden_dkg.Types.t_ReshareMsg
            Std.Hash.Random.t_RandomState)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (original_pk:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (old_pk_shares:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (tt_old: u32)
      (session_id: Golden_dkg.Types.t_SessionId)
    : Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_ReshareError =
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32 Golden_dkg.Types.t_ReshareMsg Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          received
        <:
        Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_ReshareMsg)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let (sender_id: u32), (msg: Golden_dkg.Types.t_ReshareMsg) = temp_1_ in
          if
            msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_session_id <>. session_id
            <:
            bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err
                (Golden_dkg.Error.ReshareError_SessionMismatch
                  ({ Golden_dkg.Error.f_sender = sender_id })
                  <:
                  Golden_dkg.Error.t_ReshareError)
                <:
                Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                  Golden_dkg.Error.t_ReshareError)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                    Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                      Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                      Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_ReshareError)
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    if
      (cast (Std.Collections.Hash.Map.impl_1__len #u32
              #Golden_dkg.Types.t_ReshareMsg
              #Std.Hash.Random.t_RandomState
              received
            <:
            usize)
        <:
        u32) <.
      tt_old
    then
      Core_models.Result.Result_Err
      (Golden_dkg.Error.ReshareError_InsufficientDealers
        ({
            Golden_dkg.Error.f_needed = tt_old;
            Golden_dkg.Error.f_got
            =
            cast (Std.Collections.Hash.Map.impl_1__len #u32
                  #Golden_dkg.Types.t_ReshareMsg
                  #Std.Hash.Random.t_RandomState
                  received
                <:
                usize)
            <:
            u32
          })
        <:
        Golden_dkg.Error.t_ReshareError)
      <:
      Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_ReshareError
    else
      match
        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                  u32 Golden_dkg.Types.t_ReshareMsg Std.Hash.Random.t_RandomState)
              #FStar.Tactics.Typeclasses.solve
              received
            <:
            Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_ReshareMsg)
          ()
          (fun temp_0_ temp_1_ ->
              let _:Prims.unit = temp_0_ in
              let (sender_id: u32), (msg: Golden_dkg.Types.t_ReshareMsg) = temp_1_ in
              match
                Std.Collections.Hash.Map.impl_2__get #u32
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #Std.Hash.Random.t_RandomState
                  #u32
                  old_pk_shares
                  sender_id
                <:
                Core_models.Option.t_Option
                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              with
              | Core_models.Option.Option_Some expected_pk_share ->
                if
                  (msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_vss_commitment.[ mk_usize
                      0 ]
                    <:
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) <>.
                  expected_pk_share
                  <:
                  bool
                then
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Result.Result_Err
                      (Golden_dkg.Error.ReshareError_CiphertextVerificationFailed
                        ({
                            Golden_dkg.Error.f_sender = sender_id;
                            Golden_dkg.Error.f_recipient = new_id
                          })
                        <:
                        Golden_dkg.Error.t_ReshareError)
                      <:
                      Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                        Golden_dkg.Error.t_ReshareError)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                          Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit)) Prims.unit
                else
                  (match
                      Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                            #(Std.Collections.Hash.Map.t_HashMap u32
                                Golden_dkg.Types.t_Ciphertext
                                Std.Hash.Random.t_RandomState)
                            #FStar.Tactics.Typeclasses.solve
                            msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_ciphertexts
                          <:
                          Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
                        ()
                        (fun temp_0_ temp_1_ ->
                            let _:Prims.unit = temp_0_ in
                            let (recipient_id: u32), (ct: Golden_dkg.Types.t_Ciphertext) =
                              temp_1_
                            in
                            let expected_share_comm:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config =
                              Golden_dkg.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                                      .Golden_dkg.Types.f_reshare_header
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
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
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
                                        expected_share_comm
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
                                  (Golden_dkg.Error.ReshareError_CiphertextVerificationFailed
                                    ({
                                        Golden_dkg.Error.f_sender = sender_id;
                                        Golden_dkg.Error.f_recipient = recipient_id
                                      })
                                    <:
                                    Golden_dkg.Error.t_ReshareError)
                                  <:
                                  Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError)
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                      Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                        Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                                Prims.unit
                            else
                              Core_models.Ops.Control_flow.ControlFlow_Continue ()
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                        Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                                Prims.unit)
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError) Prims.unit
                    with
                    | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break ret
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                              Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                        Prims.unit
                    | Core_models.Ops.Control_flow.ControlFlow_Continue loop_res ->
                      Core_models.Ops.Control_flow.ControlFlow_Continue loop_res
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                        Prims.unit)
              | _ ->
                match
                  Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                        #(Std.Collections.Hash.Map.t_HashMap u32
                            Golden_dkg.Types.t_Ciphertext
                            Std.Hash.Random.t_RandomState)
                        #FStar.Tactics.Typeclasses.solve
                        msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_ciphertexts
                      <:
                      Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_Ciphertext)
                    ()
                    (fun temp_0_ temp_1_ ->
                        let _:Prims.unit = temp_0_ in
                        let (recipient_id: u32), (ct: Golden_dkg.Types.t_Ciphertext) = temp_1_ in
                        let expected_share_comm:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config =
                          Golden_dkg.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                                  .Golden_dkg.Types.f_reshare_header
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
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
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
                                    expected_share_comm
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
                              (Golden_dkg.Error.ReshareError_CiphertextVerificationFailed
                                ({
                                    Golden_dkg.Error.f_sender = sender_id;
                                    Golden_dkg.Error.f_recipient = recipient_id
                                  })
                                <:
                                Golden_dkg.Error.t_ReshareError)
                              <:
                              Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                Golden_dkg.Error.t_ReshareError)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                  Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                            Prims.unit
                        else
                          Core_models.Ops.Control_flow.ControlFlow_Continue ()
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                            Prims.unit)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                        Golden_dkg.Error.t_ReshareError) Prims.unit
                with
                | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break ret
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                          Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit)) Prims.unit
                | Core_models.Ops.Control_flow.ControlFlow_Continue loop_res ->
                  Core_models.Ops.Control_flow.ControlFlow_Continue loop_res
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError) (Prims.unit & Prims.unit)) Prims.unit)
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput Golden_dkg.Error.t_ReshareError)
          Prims.unit
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
        let
        (sub_shares:
          Alloc.Vec.t_Vec
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
          (u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          Alloc.Alloc.t_Global =
          Alloc.Vec.impl__new #(u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            ()
        in
        match
          Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                    u32 Golden_dkg.Types.t_ReshareMsg Std.Hash.Random.t_RandomState)
                #FStar.Tactics.Typeclasses.solve
                received
              <:
              Std.Collections.Hash.Map.t_Iter u32 Golden_dkg.Types.t_ReshareMsg)
            sub_shares
            (fun sub_shares temp_1_ ->
                let sub_shares:Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global =
                  sub_shares
                in
                let (sender_id: u32), (msg: Golden_dkg.Types.t_ReshareMsg) = temp_1_ in
                match
                  Core_models.Option.impl__ok_or #Golden_dkg.Types.t_Ciphertext
                    #Golden_dkg.Error.t_ReshareError
                    (Std.Collections.Hash.Map.impl_2__get #u32
                        #Golden_dkg.Types.t_Ciphertext
                        #Std.Hash.Random.t_RandomState
                        #u32
                        msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_ciphertexts
                        new_id
                      <:
                      Core_models.Option.t_Option Golden_dkg.Types.t_Ciphertext)
                    (Golden_dkg.Error.ReshareError_MissingCiphertext
                      ({
                          Golden_dkg.Error.f_sender = sender_id;
                          Golden_dkg.Error.f_recipient = new_id
                        })
                      <:
                      Golden_dkg.Error.t_ReshareError)
                  <:
                  Core_models.Result.t_Result Golden_dkg.Types.t_Ciphertext
                    Golden_dkg.Error.t_ReshareError
                with
                | Core_models.Result.Result_Ok ct ->
                  let sender_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                  Ark_bls12_381_.Curves.G1.t_Config =
                    old_members.[ sender_id ]
                  in
                  let
                  (r_pad:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                  (_:
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) =
                    Golden_dkg.Evrf.derive_pad new_sk_identity
                      sender_pk
                      (msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_random_msg
                        <:
                        t_Slice u8)
                      beta
                  in
                  let decrypted:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      ct.Golden_dkg.Types.f_encrypted_share
                      r_pad
                  in
                  let sub_shares:Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_1__push #(u32 &
                        Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #Alloc.Alloc.t_Global
                      sub_shares
                      (sender_id, decrypted
                        <:
                        (u32 &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  in
                  Core_models.Ops.Control_flow.ControlFlow_Continue sub_shares
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError)
                        (Prims.unit &
                          Alloc.Vec.t_Vec
                            (u32 &
                              Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            Alloc.Alloc.t_Global))
                    (Alloc.Vec.t_Vec
                        (u32 &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        Alloc.Alloc.t_Global)
                | Core_models.Result.Result_Err err ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                        Golden_dkg.Error.t_ReshareError)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                          Golden_dkg.Error.t_ReshareError)
                      (Prims.unit &
                        Alloc.Vec.t_Vec
                          (u32 &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                          Alloc.Alloc.t_Global))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError)
                        (Prims.unit &
                          Alloc.Vec.t_Vec
                            (u32 &
                              Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            Alloc.Alloc.t_Global))
                    (Alloc.Vec.t_Vec
                        (u32 &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        Alloc.Alloc.t_Global))
          <:
          Core_models.Ops.Control_flow.t_ControlFlow
            (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                Golden_dkg.Error.t_ReshareError)
            (Alloc.Vec.t_Vec
                (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                Alloc.Alloc.t_Global)
        with
        | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
        | Core_models.Ops.Control_flow.ControlFlow_Continue sub_shares ->
          let new_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #u64
              #FStar.Tactics.Typeclasses.solve
              (mk_u64 0)
          in
          match
            Rust_primitives.Hax.Folds.fold_enumerated_slice_return (Alloc.Vec.impl_1__as_slice sub_shares

                <:
                t_Slice
                (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              (fun new_secret_share temp_1_ ->
                  let new_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    new_secret_share
                  in
                  let _:usize = temp_1_ in
                  true)
              new_secret_share
              (fun new_secret_share temp_1_ ->
                  let new_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    new_secret_share
                  in
                  let
                  (idx: usize),
                  ((xi_id: u32),
                    (sub_share:
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
                    temp_1_
                  in
                  let xi:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #u64
                      #FStar.Tactics.Typeclasses.solve
                      (cast (xi_id <: u32) <: u64)
                  in
                  let li:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #u64
                      #FStar.Tactics.Typeclasses.solve
                      (mk_u64 1)
                  in
                  match
                    Rust_primitives.Hax.Folds.fold_enumerated_slice_return (Alloc.Vec.impl_1__as_slice
                          sub_shares
                        <:
                        t_Slice
                        (u32 &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (fun li temp_1_ ->
                          let li:Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                            li
                          in
                          let _:usize = temp_1_ in
                          true)
                      li
                      (fun li temp_1_ ->
                          let li:Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                            li
                          in
                          let
                          (jdx: usize),
                          ((xj_id: u32),
                            (_:
                              Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                          =
                            temp_1_
                          in
                          if idx =. jdx <: bool
                          then
                            Core_models.Ops.Control_flow.ControlFlow_Continue li
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                      Golden_dkg.Error.t_ReshareError)
                                  (Prims.unit &
                                    Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4)))
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              )
                          else
                            let xj:Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                              Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
                                #u64
                                #FStar.Tactics.Typeclasses.solve
                                (cast (xj_id <: u32) <: u64)
                            in
                            match
                              Core_models.Option.impl__ok_or #(Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
                                #Golden_dkg.Error.t_ReshareError
                                (Ark_ff.Fields.f_inverse #(Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                    #FStar.Tactics.Typeclasses.solve
                                    (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4))
                                        #(Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4))
                                        #FStar.Tactics.Typeclasses.solve
                                        xj
                                        xi
                                      <:
                                      Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                  <:
                                  Core_models.Option.t_Option
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4)))
                                (Golden_dkg.Error.ReshareError_DuplicateNodeIndex
                                  ({ Golden_dkg.Error.f_index = xi_id })
                                  <:
                                  Golden_dkg.Error.t_ReshareError)
                              <:
                              Core_models.Result.t_Result
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)) Golden_dkg.Error.t_ReshareError
                            with
                            | Core_models.Result.Result_Ok hoist41 ->
                              let li:Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                                Core_models.Ops.Arith.f_mul_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                                  #(Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                                  #FStar.Tactics.Typeclasses.solve
                                  li
                                  (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4))
                                      #FStar.Tactics.Typeclasses.solve
                                      xj
                                      hoist41
                                    <:
                                    Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))
                              in
                              Core_models.Ops.Control_flow.ControlFlow_Continue li
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                        Golden_dkg.Error.t_ReshareError)
                                    (Prims.unit &
                                      Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
                            | Core_models.Result.Result_Err err ->
                              Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Ops.Control_flow.ControlFlow_Break
                                (Core_models.Result.Result_Err err
                                  <:
                                  Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError)
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                      Golden_dkg.Error.t_ReshareError)
                                  (Prims.unit &
                                    Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4)))
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                        Golden_dkg.Error.t_ReshareError)
                                    (Prims.unit &
                                      Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4)))
                                (Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4)))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                          Golden_dkg.Error.t_ReshareError)
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  with
                  | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                    Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Ops.Control_flow.ControlFlow_Break ret
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                            Golden_dkg.Error.t_ReshareError)
                        (Prims.unit &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                              Golden_dkg.Error.t_ReshareError)
                          (Prims.unit &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  | Core_models.Ops.Control_flow.ControlFlow_Continue li ->
                    Core_models.Ops.Control_flow.ControlFlow_Continue
                    (Core_models.Ops.Arith.f_add_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        new_secret_share
                        (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #FStar.Tactics.Typeclasses.solve
                            sub_share
                            li
                          <:
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                              Golden_dkg.Error.t_ReshareError)
                          (Prims.unit &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                  Golden_dkg.Error.t_ReshareError)
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          with
          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
          | Core_models.Ops.Control_flow.ControlFlow_Continue new_secret_share ->
            let
            (_: Std.Collections.Hash.Map.t_Values u32 Golden_dkg.Types.t_ReshareMsg),
            (out: Core_models.Option.t_Option Golden_dkg.Types.t_ReshareMsg) =
              Core_models.Iter.Traits.Iterator.f_next #(Std.Collections.Hash.Map.t_Values u32
                    Golden_dkg.Types.t_ReshareMsg)
                #FStar.Tactics.Typeclasses.solve
                (Std.Collections.Hash.Map.impl_1__values #u32
                    #Golden_dkg.Types.t_ReshareMsg
                    #Std.Hash.Random.t_RandomState
                    received
                  <:
                  Std.Collections.Hash.Map.t_Values u32 Golden_dkg.Types.t_ReshareMsg)
            in
            match
              Core_models.Option.impl__ok_or #Golden_dkg.Types.t_ReshareMsg
                #Golden_dkg.Error.t_ReshareError
                out
                (Golden_dkg.Error.ReshareError_NoMessages <: Golden_dkg.Error.t_ReshareError)
              <:
              Core_models.Result.t_Result Golden_dkg.Types.t_ReshareMsg
                Golden_dkg.Error.t_ReshareError
            with
            | Core_models.Result.Result_Ok first_msg ->
              let (new_member_ids: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u32
                Alloc.Alloc.t_Global =
                Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Copied.t_Copied
                    (Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext))
                  #FStar.Tactics.Typeclasses.solve
                  #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
                  (Core_models.Iter.Traits.Iterator.f_copied #(Std.Collections.Hash.Map.t_Keys u32
                          Golden_dkg.Types.t_Ciphertext)
                      #FStar.Tactics.Typeclasses.solve
                      #u32
                      (Std.Collections.Hash.Map.impl_1__keys #u32
                          #Golden_dkg.Types.t_Ciphertext
                          #Std.Hash.Random.t_RandomState
                          first_msg.Golden_dkg.Types.f_reshare_header.Golden_dkg.Types.f_ciphertexts
                        <:
                        Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext)
                    <:
                    Core_models.Iter.Adapters.Copied.t_Copied
                    (Std.Collections.Hash.Map.t_Keys u32 Golden_dkg.Types.t_Ciphertext))
              in
              let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState =
                Std.Collections.Hash.Map.impl__new #u32
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  ()
              in
              (match
                  Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                        #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
                        #FStar.Tactics.Typeclasses.solve
                        new_member_ids
                      <:
                      Core_models.Slice.Iter.t_Iter u32)
                    public_key_shares
                    (fun public_key_shares k ->
                        let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)
                          Std.Hash.Random.t_RandomState =
                          public_key_shares
                        in
                        let k:u32 = k in
                        let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config =
                          Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                              Ark_bls12_381_.Curves.G1.t_Config)
                            #FStar.Tactics.Typeclasses.solve
                            ()
                        in
                        match
                          Rust_primitives.Hax.Folds.fold_enumerated_slice_return (Alloc.Vec.impl_1__as_slice
                                sub_shares
                              <:
                              t_Slice
                              (u32 &
                                Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              ))
                            (fun pk_k temp_1_ ->
                                let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                Ark_bls12_381_.Curves.G1.t_Config =
                                  pk_k
                                in
                                let _:usize = temp_1_ in
                                true)
                            pk_k
                            (fun pk_k temp_1_ ->
                                let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                Ark_bls12_381_.Curves.G1.t_Config =
                                  pk_k
                                in
                                let
                                (idx: usize),
                                ((sender_id: u32),
                                  (_:
                                    Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))) =
                                  temp_1_
                                in
                                let xi:Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                                =
                                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                    #u64
                                    #FStar.Tactics.Typeclasses.solve
                                    (cast (sender_id <: u32) <: u64)
                                in
                                let li:Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                                =
                                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                    #u64
                                    #FStar.Tactics.Typeclasses.solve
                                    (mk_u64 1)
                                in
                                match
                                  Rust_primitives.Hax.Folds.fold_enumerated_slice_return (Alloc.Vec.impl_1__as_slice
                                        sub_shares
                                      <:
                                      t_Slice
                                      (u32 &
                                        Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4)))
                                    (fun li temp_1_ ->
                                        let li:Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4) =
                                          li
                                        in
                                        let _:usize = temp_1_ in
                                        true)
                                    li
                                    (fun li temp_1_ ->
                                        let li:Ark_ff.Fields.Models.Fp.t_Fp
                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                          (mk_usize 4) =
                                          li
                                        in
                                        let
                                        (jdx: usize),
                                        ((xj_id: u32),
                                          (_:
                                            Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))) =
                                          temp_1_
                                        in
                                        if idx =. jdx <: bool
                                        then
                                          Core_models.Ops.Control_flow.ControlFlow_Continue li
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Result.t_Result
                                                    Golden_dkg.Types.t_DkgOutput
                                                    Golden_dkg.Error.t_ReshareError)
                                                (Prims.unit &
                                                  Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                            (Ark_ff.Fields.Models.Fp.t_Fp
                                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)
                                                ) (mk_usize 4))
                                        else
                                          let xj:Ark_ff.Fields.Models.Fp.t_Fp
                                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                            (mk_usize 4) =
                                            Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                              #u64
                                              #FStar.Tactics.Typeclasses.solve
                                              (cast (xj_id <: u32) <: u64)
                                          in
                                          match
                                            Core_models.Option.impl__ok_or #(Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                              #Golden_dkg.Error.t_ReshareError
                                              (Ark_ff.Fields.f_inverse #(Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4))
                                                  #FStar.Tactics.Typeclasses.solve
                                                  (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4))
                                                      #(Ark_ff.Fields.Models.Fp.t_Fp
                                                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                              Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                              (mk_usize 4)) (mk_usize 4))
                                                      #FStar.Tactics.Typeclasses.solve
                                                      xj
                                                      xi
                                                    <:
                                                    Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4))
                                                <:
                                                Core_models.Option.t_Option
                                                (Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                              (Golden_dkg.Error.ReshareError_DuplicateNodeIndex
                                                ({ Golden_dkg.Error.f_index = sender_id })
                                                <:
                                                Golden_dkg.Error.t_ReshareError)
                                            <:
                                            Core_models.Result.t_Result
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                              Golden_dkg.Error.t_ReshareError
                                          with
                                          | Core_models.Result.Result_Ok hoist45 ->
                                            let li:Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4) =
                                              Core_models.Ops.Arith.f_mul_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4))
                                                #(Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4))
                                                #FStar.Tactics.Typeclasses.solve
                                                li
                                                (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4))
                                                    #(Ark_ff.Fields.Models.Fp.t_Fp
                                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                            Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                            (mk_usize 4)) (mk_usize 4))
                                                    #FStar.Tactics.Typeclasses.solve
                                                    xj
                                                    hoist45
                                                  <:
                                                  Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4))
                                            in
                                            Core_models.Ops.Control_flow.ControlFlow_Continue li
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Result.t_Result
                                                      Golden_dkg.Types.t_DkgOutput
                                                      Golden_dkg.Error.t_ReshareError)
                                                  (Prims.unit &
                                                    Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4)))
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4))
                                          | Core_models.Result.Result_Err err ->
                                            Core_models.Ops.Control_flow.ControlFlow_Break
                                            (Core_models.Ops.Control_flow.ControlFlow_Break
                                              (Core_models.Result.Result_Err err
                                                <:
                                                Core_models.Result.t_Result
                                                  Golden_dkg.Types.t_DkgOutput
                                                  Golden_dkg.Error.t_ReshareError)
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Result.t_Result
                                                    Golden_dkg.Types.t_DkgOutput
                                                    Golden_dkg.Error.t_ReshareError)
                                                (Prims.unit &
                                                  Ark_ff.Fields.Models.Fp.t_Fp
                                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                        Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                        (mk_usize 4)) (mk_usize 4)))
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Result.t_Result
                                                      Golden_dkg.Types.t_DkgOutput
                                                      Golden_dkg.Error.t_ReshareError)
                                                  (Prims.unit &
                                                    Ark_ff.Fields.Models.Fp.t_Fp
                                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                          Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                          (mk_usize 4)) (mk_usize 4)))
                                              (Ark_ff.Fields.Models.Fp.t_Fp
                                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                      Ark_bls12_381_.Fields.Fr.t_FrConfig
                                                      (mk_usize 4)) (mk_usize 4)))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                        Golden_dkg.Error.t_ReshareError)
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                with
                                | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Break ret
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                          Golden_dkg.Error.t_ReshareError)
                                      (Prims.unit &
                                        Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                        Ark_bls12_381_.Curves.G1.t_Config))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                            Golden_dkg.Error.t_ReshareError)
                                        (Prims.unit &
                                          Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                          Ark_bls12_381_.Curves.G1.t_Config))
                                    (Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                      Ark_bls12_381_.Curves.G1.t_Config)
                                | Core_models.Ops.Control_flow.ControlFlow_Continue li ->
                                  let msg:Golden_dkg.Types.t_ReshareMsg = received.[ sender_id ] in
                                  let share_comm:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config =
                                    Golden_dkg.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice
                                          msg.Golden_dkg.Types.f_reshare_header
                                            .Golden_dkg.Types.f_vss_commitment
                                        <:
                                        t_Slice
                                        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                          Ark_bls12_381_.Curves.G1.t_Config))
                                      k
                                  in
                                  Core_models.Ops.Control_flow.ControlFlow_Continue
                                  (Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                        Ark_bls12_381_.Curves.G1.t_Config)
                                      #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                        Ark_bls12_381_.Curves.G1.t_Config)
                                      #FStar.Tactics.Typeclasses.solve
                                      pk_k
                                      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                            Ark_bls12_381_.Curves.G1.t_Config)
                                          #(Ark_ff.Fields.Models.Fp.t_Fp
                                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                              (mk_usize 4))
                                          #FStar.Tactics.Typeclasses.solve
                                          (Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                                Ark_bls12_381_.Curves.G1.t_Config)
                                              #FStar.Tactics.Typeclasses.solve
                                              share_comm
                                            <:
                                            Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                            Ark_bls12_381_.Curves.G1.t_Config)
                                          li
                                        <:
                                        Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                        Ark_bls12_381_.Curves.G1.t_Config))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                            Golden_dkg.Error.t_ReshareError)
                                        (Prims.unit &
                                          Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                          Ark_bls12_381_.Curves.G1.t_Config))
                                    (Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                      Ark_bls12_381_.Curves.G1.t_Config))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                Golden_dkg.Error.t_ReshareError)
                            (Ark_ec.Models.Short_weierstrass.Group.t_Projective
                              Ark_bls12_381_.Curves.G1.t_Config)
                        with
                        | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                          Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Ops.Control_flow.ControlFlow_Break ret
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                  Golden_dkg.Error.t_ReshareError)
                              (Prims.unit &
                                Std.Collections.Hash.Map.t_HashMap u32
                                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)
                                  Std.Hash.Random.t_RandomState))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError)
                                (Prims.unit &
                                  Std.Collections.Hash.Map.t_HashMap u32
                                    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                      Ark_bls12_381_.Curves.G1.t_Config)
                                    Std.Hash.Random.t_RandomState))
                            (Std.Collections.Hash.Map.t_HashMap u32
                                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config)
                                Std.Hash.Random.t_RandomState)
                        | Core_models.Ops.Control_flow.ControlFlow_Continue pk_k ->
                          let
                          (tmp0:
                            Std.Collections.Hash.Map.t_HashMap u32
                              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                              Std.Hash.Random.t_RandomState),
                          (out:
                            Core_models.Option.t_Option
                            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)) =
                            Std.Collections.Hash.Map.impl_2__insert #u32
                              #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                              #Std.Hash.Random.t_RandomState
                              public_key_shares
                              k
                              (Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                    Ark_bls12_381_.Curves.G1.t_Config)
                                  #FStar.Tactics.Typeclasses.solve
                                  pk_k
                                <:
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                          in
                          let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
                            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)
                            Std.Hash.Random.t_RandomState =
                            tmp0
                          in
                          let _:Core_models.Option.t_Option
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config) =
                            out
                          in
                          Core_models.Ops.Control_flow.ControlFlow_Continue public_key_shares
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                                    Golden_dkg.Error.t_ReshareError)
                                (Prims.unit &
                                  Std.Collections.Hash.Map.t_HashMap u32
                                    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                      Ark_bls12_381_.Curves.G1.t_Config)
                                    Std.Hash.Random.t_RandomState))
                            (Std.Collections.Hash.Map.t_HashMap u32
                                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config)
                                Std.Hash.Random.t_RandomState))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                        Golden_dkg.Error.t_ReshareError)
                    (Std.Collections.Hash.Map.t_HashMap u32
                        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        Std.Hash.Random.t_RandomState)
                with
                | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                | Core_models.Ops.Control_flow.ControlFlow_Continue public_key_shares ->
                  Core_models.Result.Result_Ok
                  ({
                      Golden_dkg.Types.f_public_key = original_pk;
                      Golden_dkg.Types.f_public_key_shares = public_key_shares;
                      Golden_dkg.Types.f_secret_share = new_secret_share
                    }
                    <:
                    Golden_dkg.Types.t_DkgOutput)
                  <:
                  Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                    Golden_dkg.Error.t_ReshareError)
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Golden_dkg.Types.t_DkgOutput
                Golden_dkg.Error.t_ReshareError
