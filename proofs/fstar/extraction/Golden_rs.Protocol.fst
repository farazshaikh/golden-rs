module Golden_rs.Protocol
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
  let open Ark_std.Rand_helper in
  let open Rand.Distributions.Distribution in
  let open Rand.Rng in
  let open Std.Collections.Hash.Map in
  let open Std.Hash.Random in
  let open Tracing_core.Callsite in
  let open Tracing_core.Metadata in
  ()

/// Execute Round 0 of the Golden DKG protocol for a single node.
/// Per Figure 4 of the Golden paper (IACR 2025/1924), Round0(n, t, i, sk_i^I, {(j, PK_j^I)}):
/// > "1. omega_i <- random Z_p
/// >  2. {x_bar_{i,j}}, C_bar_i <- Shamir.Share(omega_i, n, t)
/// >  3. msg_i <- random {0,1}^lambda
/// >  4-7. For each peer: eVRF.Evaluate, encrypt share z_{i,j} = r_{i,j} + x_bar_{i,j}
/// >  8. st_i <- x_bar_{i,i}
/// >  9-10. Broadcast"
/// Returns the broadcast message and this node's own Shamir share (`st_i`).
let round0
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (id n t: u32)
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (rng: iimpl_1039969868_)
      (session_id: t_Array u8 (mk_usize 32))
    : (iimpl_1039969868_ &
      (Golden_rs.Types.t_Round0Msg &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
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
  let omega:Golden_rs.Types.t_SecretScalar = Golden_rs.Types.impl_SecretScalar__new out in
  let (tmp0: iimpl_1039969868_), (out: Golden_rs.Shamir.t_Polynomial) =
    Golden_rs.Shamir.impl_Polynomial__new_random #iimpl_1039969868_
      (Golden_rs.Types.impl_SecretScalar__inner omega
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (cast (t -! mk_u32 1 <: u32) <: usize)
      rng
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let poly:Golden_rs.Shamir.t_Polynomial = out in
  let vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Golden_rs.Vss.commit poly
  in
  let
  (all_shares:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      Std.Hash.Random.t_RandomState):Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    Std.Hash.Random.t_RandomState =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Ops.Range.t_RangeInclusive u32)
          (u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
      #FStar.Tactics.Typeclasses.solve
      #(Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          Std.Hash.Random.t_RandomState)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Ops.Range.t_RangeInclusive u32)
          #FStar.Tactics.Typeclasses.solve
          #(u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (Core_models.Ops.Range.impl_7__new #u32 (mk_u32 1) n
            <:
            Core_models.Ops.Range.t_RangeInclusive u32)
          (fun j ->
              let j:u32 = j in
              j,
              (Golden_rs.Shamir.impl_Polynomial__evaluate poly
                  (Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #u64
                      #FStar.Tactics.Typeclasses.solve
                      (cast (j <: u32) <: u64)
                    <:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              <:
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Core_models.Iter.Adapters.Map.t_Map (Core_models.Ops.Range.t_RangeInclusive u32)
          (u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
  in
  let own_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    all_shares.[ id ]
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
    Golden_rs.Types.t_Ciphertext
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32 #Golden_rs.Types.t_Ciphertext ()
  in
  let
  (peer_pads:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Std.Hash.Random.t_RandomState):Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      ()
  in
  let
  (ciphertexts:
    Std.Collections.Hash.Map.t_HashMap u32
      Golden_rs.Types.t_Ciphertext
      Std.Hash.Random.t_RandomState),
  (peer_pads:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Std.Hash.Random.t_RandomState) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          peers
        <:
        Std.Collections.Hash.Map.t_Iter u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (ciphertexts, peer_pads
        <:
        (Std.Collections.Hash.Map.t_HashMap u32
            Golden_rs.Types.t_Ciphertext
            Std.Hash.Random.t_RandomState &
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState))
      (fun temp_0_ temp_1_ ->
          let
          (ciphertexts:
            Std.Collections.Hash.Map.t_HashMap u32
              Golden_rs.Types.t_Ciphertext
              Std.Hash.Random.t_RandomState),
          (peer_pads:
            Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState) =
            temp_0_
          in
          let
          (peer_id: u32),
          (peer_pk:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
            temp_1_
          in
          if peer_id =. id <: bool
          then
            ciphertexts, peer_pads
            <:
            (Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState &
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState)
          else
            let
            (r_pad:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
            (r_commitment:
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
              Golden_rs.Evrf.derive_pad sk peer_pk (random_msg <: t_Slice u8) beta
            in
            let
            (tmp0:
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState),
            (out:
              Core_models.Option.t_Option
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
            =
              Std.Collections.Hash.Map.impl_2__insert #u32
                #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                #Std.Hash.Random.t_RandomState
                peer_pads
                peer_id
                (r_pad, r_commitment
                  <:
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config))
            in
            let peer_pads:Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState =
              tmp0
            in
            let _:Core_models.Option.t_Option
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
              out
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
                (all_shares.[ peer_id ]
                  <:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            in
            let
            (tmp0:
              Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState),
            (out: Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext) =
              Std.Collections.Hash.Map.impl_2__insert #u32
                #Golden_rs.Types.t_Ciphertext
                #Std.Hash.Random.t_RandomState
                ciphertexts
                peer_id
                ({
                    Golden_rs.Types.f_r_commitment = r_commitment;
                    Golden_rs.Types.f_encrypted_share = encrypted_share
                  }
                  <:
                  Golden_rs.Types.t_Ciphertext)
            in
            let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
              Golden_rs.Types.t_Ciphertext
              Std.Hash.Random.t_RandomState =
              tmp0
            in
            let _:Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext = out in
            ciphertexts, peer_pads
            <:
            (Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState &
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState))
  in
  let my_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    peers.[ id ]
  in
  let
  (peers_for_proof:
    Alloc.Vec.t_Vec
      (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec
          (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          #FStar.Tactics.Typeclasses.solve
          #(u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(
                (u32 &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          )
          (Core_models.Iter.Traits.Iterator.f_filter #(Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              #FStar.Tactics.Typeclasses.solve
              #(
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool)
              (Std.Collections.Hash.Map.impl_1__iter #u32
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #Std.Hash.Random.t_RandomState
                  peers
                <:
                Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (fun temp_0_ ->
                  let
                  (pid: u32),
                  (_:
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) =
                    temp_0_
                  in
                  pid <>. id <: bool)
            <:
            Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          (fun temp_0_ ->
              let
              (pid: u32),
              (pk:
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
                temp_0_
              in
              pid, pk
              <:
              (u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
  in
  let
  (pads_for_proof:
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
          (Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
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
      (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          #FStar.Tactics.Typeclasses.solve
          #(u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          )
          (Std.Collections.Hash.Map.impl_1__iter #u32
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              #Std.Hash.Random.t_RandomState
              peer_pads
            <:
            Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (fun temp_0_ ->
              let
              (pid: u32),
              ((r:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                (rc:
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              ) =
                temp_0_
              in
              pid, r, rc
              <:
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
  in
  let evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
    Golden_rs.Zk_evrf.t_EVRFProof
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32 #Golden_rs.Zk_evrf.t_EVRFProof ()
  in
  let batch_evrf_proof:Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof =
    Core_models.Result.impl__ok #Golden_rs.Zk_evrf.t_EVRFProof
      #Alloc.String.t_String
      (Golden_rs.Zk_evrf.prove_evrf_batch sk
          my_pk
          (Alloc.Vec.impl_1__as_slice peers_for_proof
            <:
            t_Slice
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          (Alloc.Vec.impl_1__as_slice pads_for_proof
            <:
            t_Slice
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          beta
        <:
        Core_models.Result.t_Result Golden_rs.Zk_evrf.t_EVRFProof Alloc.String.t_String)
  in
  let msg:Golden_rs.Types.t_Round0Msg =
    {
      Golden_rs.Types.f_session_id = session_id;
      Golden_rs.Types.f_from = id;
      Golden_rs.Types.f_random_msg = random_msg;
      Golden_rs.Types.f_vss_commitment = vss_commitment;
      Golden_rs.Types.f_ciphertexts = ciphertexts;
      Golden_rs.Types.f_evrf_proofs = evrf_proofs;
      Golden_rs.Types.f_batch_evrf_proof = batch_evrf_proof
    }
    <:
    Golden_rs.Types.t_Round0Msg
  in
  let hax_temp_output:(Golden_rs.Types.t_Round0Msg &
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    msg, own_share
    <:
    (Golden_rs.Types.t_Round0Msg &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  in
  rng, hax_temp_output
  <:
  (iimpl_1039969868_ &
    (Golden_rs.Types.t_Round0Msg &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))

/// Error type for protocol verification failures.
type t_ProtocolError =
  | ProtocolError_CiphertextVerificationFailed {
    f_sender:u32;
    f_recipient:u32
  }: t_ProtocolError
  | ProtocolError_MissingCiphertext {
    f_sender:u32;
    f_recipient:u32
  }: t_ProtocolError
  | ProtocolError_ZeroSecretViolation { f_sender:u32 }: t_ProtocolError
  | ProtocolError_PeerCountMismatch {
    f_expected:u32;
    f_got:usize
  }: t_ProtocolError
  | ProtocolError_BroadcastReceiveFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_ProtocolError
  | ProtocolError_RegistrationFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_ProtocolError
  | ProtocolError_SessionMismatch { f_sender:u32 }: t_ProtocolError

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_ProtocolError

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Fmt.t_Display t_ProtocolError =
  {
    f_fmt_pre = (fun (self: t_ProtocolError) (f: Core_models.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_ProtocolError)
        (f: Core_models.Fmt.t_Formatter)
        (out1:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_ProtocolError) (f: Core_models.Fmt.t_Formatter) ->
      let args:t_ProtocolError = self <: t_ProtocolError in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_debug #t_ProtocolError args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let
      (tmp0: Core_models.Fmt.t_Formatter),
      (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
        Core_models.Fmt.impl_11__write_fmt f
          (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
              (mk_usize 1)
              (let list = [""] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let f:Core_models.Fmt.t_Formatter = tmp0 in
      let hax_temp_output:Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error = out in
      f, hax_temp_output
      <:
      (Core_models.Fmt.t_Formatter & Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Error.t_Error t_ProtocolError =
  { _super_i0 = FStar.Tactics.Typeclasses.solve; _super_i1 = FStar.Tactics.Typeclasses.solve }

/// Execute Round 0 for key refresh (zero secret sharing).
/// Per Section 5.2 of the Golden paper (IACR 2025/1924):
/// > "Instead of sampling omega_i at random, set omega_i = 0"
/// Identical to [`round0`] but with `omega = 0`. The polynomial `f_i` has
/// `f_i(0) = 0`, so `A_{i,0} = g^0 = identity`. The node's existing share
/// is NOT modified here -- the delta is applied in [`round1_refresh`].
let round0_refresh
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (id n t: u32)
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (rng: iimpl_1039969868_)
      (session_id: t_Array u8 (mk_usize 32))
    : (iimpl_1039969868_ &
      (Golden_rs.Types.t_Round0Msg &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
  let omega:Golden_rs.Types.t_SecretScalar =
    Golden_rs.Types.impl_SecretScalar__new (Ark_ff.Fields.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  in
  let (tmp0: iimpl_1039969868_), (out: Golden_rs.Shamir.t_Polynomial) =
    Golden_rs.Shamir.impl_Polynomial__new_random #iimpl_1039969868_
      (Golden_rs.Types.impl_SecretScalar__inner omega
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (cast (t -! mk_u32 1 <: u32) <: usize)
      rng
  in
  let rng:iimpl_1039969868_ = tmp0 in
  let poly:Golden_rs.Shamir.t_Polynomial = out in
  let vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Golden_rs.Vss.commit poly
  in
  let
  (all_shares:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      Std.Hash.Random.t_RandomState):Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    Std.Hash.Random.t_RandomState =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Ops.Range.t_RangeInclusive u32)
          (u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
      #FStar.Tactics.Typeclasses.solve
      #(Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          Std.Hash.Random.t_RandomState)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Ops.Range.t_RangeInclusive u32)
          #FStar.Tactics.Typeclasses.solve
          #(u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (Core_models.Ops.Range.impl_7__new #u32 (mk_u32 1) n
            <:
            Core_models.Ops.Range.t_RangeInclusive u32)
          (fun j ->
              let j:u32 = j in
              j,
              (Golden_rs.Shamir.impl_Polynomial__evaluate poly
                  (Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #u64
                      #FStar.Tactics.Typeclasses.solve
                      (cast (j <: u32) <: u64)
                    <:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              <:
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Core_models.Iter.Adapters.Map.t_Map (Core_models.Ops.Range.t_RangeInclusive u32)
          (u32
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
  in
  let own_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    all_shares.[ id ]
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
    Golden_rs.Types.t_Ciphertext
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32 #Golden_rs.Types.t_Ciphertext ()
  in
  let
  (peer_pads:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Std.Hash.Random.t_RandomState):Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      ()
  in
  let
  (ciphertexts:
    Std.Collections.Hash.Map.t_HashMap u32
      Golden_rs.Types.t_Ciphertext
      Std.Hash.Random.t_RandomState),
  (peer_pads:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Std.Hash.Random.t_RandomState) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          peers
        <:
        Std.Collections.Hash.Map.t_Iter u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (ciphertexts, peer_pads
        <:
        (Std.Collections.Hash.Map.t_HashMap u32
            Golden_rs.Types.t_Ciphertext
            Std.Hash.Random.t_RandomState &
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState))
      (fun temp_0_ temp_1_ ->
          let
          (ciphertexts:
            Std.Collections.Hash.Map.t_HashMap u32
              Golden_rs.Types.t_Ciphertext
              Std.Hash.Random.t_RandomState),
          (peer_pads:
            Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState) =
            temp_0_
          in
          let
          (peer_id: u32),
          (peer_pk:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
            temp_1_
          in
          if peer_id =. id <: bool
          then
            ciphertexts, peer_pads
            <:
            (Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState &
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState)
          else
            let
            (r_pad:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
            (r_commitment:
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
              Golden_rs.Evrf.derive_pad sk peer_pk (random_msg <: t_Slice u8) beta
            in
            let
            (tmp0:
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState),
            (out:
              Core_models.Option.t_Option
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
            =
              Std.Collections.Hash.Map.impl_2__insert #u32
                #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                #Std.Hash.Random.t_RandomState
                peer_pads
                peer_id
                (r_pad, r_commitment
                  <:
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config))
            in
            let peer_pads:Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState =
              tmp0
            in
            let _:Core_models.Option.t_Option
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
              out
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
                (all_shares.[ peer_id ]
                  <:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            in
            let
            (tmp0:
              Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState),
            (out: Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext) =
              Std.Collections.Hash.Map.impl_2__insert #u32
                #Golden_rs.Types.t_Ciphertext
                #Std.Hash.Random.t_RandomState
                ciphertexts
                peer_id
                ({
                    Golden_rs.Types.f_r_commitment = r_commitment;
                    Golden_rs.Types.f_encrypted_share = encrypted_share
                  }
                  <:
                  Golden_rs.Types.t_Ciphertext)
            in
            let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
              Golden_rs.Types.t_Ciphertext
              Std.Hash.Random.t_RandomState =
              tmp0
            in
            let _:Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext = out in
            ciphertexts, peer_pads
            <:
            (Std.Collections.Hash.Map.t_HashMap u32
                Golden_rs.Types.t_Ciphertext
                Std.Hash.Random.t_RandomState &
              Std.Collections.Hash.Map.t_HashMap u32
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                Std.Hash.Random.t_RandomState))
  in
  let my_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    peers.[ id ]
  in
  let
  (peers_for_proof:
    Alloc.Vec.t_Vec
      (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec
          (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          #FStar.Tactics.Typeclasses.solve
          #(u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(
                (u32 &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          )
          (Core_models.Iter.Traits.Iterator.f_filter #(Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              #FStar.Tactics.Typeclasses.solve
              #(
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool)
              (Std.Collections.Hash.Map.impl_1__iter #u32
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #Std.Hash.Random.t_RandomState
                  peers
                <:
                Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (fun temp_0_ ->
                  let
                  (pid: u32),
                  (_:
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) =
                    temp_0_
                  in
                  pid <>. id <: bool)
            <:
            Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          (fun temp_0_ ->
              let
              (pid: u32),
              (pk:
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
                temp_0_
              in
              pid, pk
              <:
              (u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Iter.Adapters.Filter.t_Filter
              (Std.Collections.Hash.Map.t_Iter u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  ))
              (
                    (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                  -> bool))
          ((u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
  in
  let
  (pads_for_proof:
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
          (Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
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
      (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          #FStar.Tactics.Typeclasses.solve
          #(u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #(
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          )
          (Std.Collections.Hash.Map.impl_1__iter #u32
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              #Std.Hash.Random.t_RandomState
              peer_pads
            <:
            Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (fun temp_0_ ->
              let
              (pid: u32),
              ((r:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                (rc:
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              ) =
                temp_0_
              in
              pid, r, rc
              <:
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Std.Collections.Hash.Map.t_Iter u32
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          (
                (u32 &
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config))
              -> (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          ))
  in
  let evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
    Golden_rs.Zk_evrf.t_EVRFProof
    Std.Hash.Random.t_RandomState =
    Std.Collections.Hash.Map.impl__new #u32 #Golden_rs.Zk_evrf.t_EVRFProof ()
  in
  let batch_evrf_proof:Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof =
    Core_models.Result.impl__ok #Golden_rs.Zk_evrf.t_EVRFProof
      #Alloc.String.t_String
      (Golden_rs.Zk_evrf.prove_evrf_batch sk
          my_pk
          (Alloc.Vec.impl_1__as_slice peers_for_proof
            <:
            t_Slice
            (u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
            ))
          (Alloc.Vec.impl_1__as_slice pads_for_proof
            <:
            t_Slice
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          beta
        <:
        Core_models.Result.t_Result Golden_rs.Zk_evrf.t_EVRFProof Alloc.String.t_String)
  in
  let msg:Golden_rs.Types.t_Round0Msg =
    {
      Golden_rs.Types.f_session_id = session_id;
      Golden_rs.Types.f_from = id;
      Golden_rs.Types.f_random_msg = random_msg;
      Golden_rs.Types.f_vss_commitment = vss_commitment;
      Golden_rs.Types.f_ciphertexts = ciphertexts;
      Golden_rs.Types.f_evrf_proofs = evrf_proofs;
      Golden_rs.Types.f_batch_evrf_proof = batch_evrf_proof
    }
    <:
    Golden_rs.Types.t_Round0Msg
  in
  let hax_temp_output:(Golden_rs.Types.t_Round0Msg &
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    msg, own_share
    <:
    (Golden_rs.Types.t_Round0Msg &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  in
  rng, hax_temp_output
  <:
  (iimpl_1039969868_ &
    (Golden_rs.Types.t_Round0Msg &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))

let rec round1__e_ee_CALLSITE__v_META: Tracing_core.Metadata.t_Metadata =
  Tracing_core.Metadata.impl__new "event src/protocol.rs:252"
    "golden_rs::protocol"
    Tracing_core.Metadata.impl_Level__WARN
    (Core_models.Option.Option_Some "src/protocol.rs" <: Core_models.Option.t_Option string)
    (Core_models.Option.Option_Some (mk_u32 252) <: Core_models.Option.t_Option u32)
    (Core_models.Option.Option_Some "golden_rs::protocol" <: Core_models.Option.t_Option string)
    (Tracing_core.Field.impl_FieldSet__new ((let list = ["message"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice string)
        (Tracing_core.Callsite.Identifier
          (Rust_primitives.unsize round1__e_ee_CALLSITE
            <:
            dyn 1 (fun z -> Tracing_core.Callsite.t_Callsite z))
          <:
          Tracing_core.Callsite.t_Identifier)
      <:
      Tracing_core.Field.t_FieldSet)
    Tracing_core.Metadata.impl_Kind__EVENT

and round1__e_ee_CALLSITE: Tracing_core.Callsite.t_DefaultCallsite =
  Tracing_core.Callsite.impl_DefaultCallsite__new round1__e_ee_CALLSITE__v_META

let rec round1__e_ee_CALLSITE_1__v_META: Tracing_core.Metadata.t_Metadata =
  Tracing_core.Metadata.impl__new "event src/protocol.rs:272"
    "golden_rs::protocol"
    Tracing_core.Metadata.impl_Level__WARN
    (Core_models.Option.Option_Some "src/protocol.rs" <: Core_models.Option.t_Option string)
    (Core_models.Option.Option_Some (mk_u32 272) <: Core_models.Option.t_Option u32)
    (Core_models.Option.Option_Some "golden_rs::protocol" <: Core_models.Option.t_Option string)
    (Tracing_core.Field.impl_FieldSet__new ((let list = ["message"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice string)
        (Tracing_core.Callsite.Identifier
          (Rust_primitives.unsize round1__e_ee_CALLSITE_1
            <:
            dyn 1 (fun z -> Tracing_core.Callsite.t_Callsite z))
          <:
          Tracing_core.Callsite.t_Identifier)
      <:
      Tracing_core.Field.t_FieldSet)
    Tracing_core.Metadata.impl_Kind__EVENT

and round1__e_ee_CALLSITE_1: Tracing_core.Callsite.t_DefaultCallsite =
  Tracing_core.Callsite.impl_DefaultCallsite__new round1__e_ee_CALLSITE_1__v_META

let rec round1_refresh__e_ee_CALLSITE__v_META: Tracing_core.Metadata.t_Metadata =
  Tracing_core.Metadata.impl__new "event src/protocol.rs:503"
    "golden_rs::protocol"
    Tracing_core.Metadata.impl_Level__WARN
    (Core_models.Option.Option_Some "src/protocol.rs" <: Core_models.Option.t_Option string)
    (Core_models.Option.Option_Some (mk_u32 503) <: Core_models.Option.t_Option u32)
    (Core_models.Option.Option_Some "golden_rs::protocol" <: Core_models.Option.t_Option string)
    (Tracing_core.Field.impl_FieldSet__new ((let list = ["message"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice string)
        (Tracing_core.Callsite.Identifier
          (Rust_primitives.unsize round1_refresh__e_ee_CALLSITE
            <:
            dyn 1 (fun z -> Tracing_core.Callsite.t_Callsite z))
          <:
          Tracing_core.Callsite.t_Identifier)
      <:
      Tracing_core.Field.t_FieldSet)
    Tracing_core.Metadata.impl_Kind__EVENT

and round1_refresh__e_ee_CALLSITE: Tracing_core.Callsite.t_DefaultCallsite =
  Tracing_core.Callsite.impl_DefaultCallsite__new round1_refresh__e_ee_CALLSITE__v_META

let rec round1_refresh__e_ee_CALLSITE_1__v_META: Tracing_core.Metadata.t_Metadata =
  Tracing_core.Metadata.impl__new "event src/protocol.rs:522"
    "golden_rs::protocol"
    Tracing_core.Metadata.impl_Level__WARN
    (Core_models.Option.Option_Some "src/protocol.rs" <: Core_models.Option.t_Option string)
    (Core_models.Option.Option_Some (mk_u32 522) <: Core_models.Option.t_Option u32)
    (Core_models.Option.Option_Some "golden_rs::protocol" <: Core_models.Option.t_Option string)
    (Tracing_core.Field.impl_FieldSet__new ((let list = ["message"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice string)
        (Tracing_core.Callsite.Identifier
          (Rust_primitives.unsize round1_refresh__e_ee_CALLSITE_1
            <:
            dyn 1 (fun z -> Tracing_core.Callsite.t_Callsite z))
          <:
          Tracing_core.Callsite.t_Identifier)
      <:
      Tracing_core.Field.t_FieldSet)
    Tracing_core.Metadata.impl_Kind__EVENT

and round1_refresh__e_ee_CALLSITE_1: Tracing_core.Callsite.t_DefaultCallsite =
  Tracing_core.Callsite.impl_DefaultCallsite__new round1_refresh__e_ee_CALLSITE_1__v_META

/// Execute Round 1 of the Golden DKG protocol for a single node.
/// Per Figure 4 of the Golden paper (IACR 2025/1924), Round1 verification (lines 5-9):
/// > "- ABORT if eVRF.Verify fails
/// >  - X_bar_{j,k} = product A_{j,l}^{k^l} (VSS commitment to g^{f_j(k)})
/// >  - ABORT if g^{z_{j,k}} != R_{j,k} * X_bar_{j,k}"
/// Decryption (lines 10-12):
/// > "x_bar_{j,i} = z_{j,i} - r_{j,i}"
/// Aggregation (line 13):
/// > "sk_i = sum x_bar_{j,i}"
/// PK derivation (line 16):
/// > "PK = product A_{k,0}"
/// Verifies received broadcasts, decrypts shares, and produces the DKG output.
let round1
      (id: u32)
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (own_share:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (own_vss_commitment:
          Alloc.Vec.t_Vec
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Alloc.Alloc.t_Global)
      (received:
          Std.Collections.Hash.Map.t_HashMap u32
            Golden_rs.Types.t_Round0Msg
            Std.Hash.Random.t_RandomState)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (session_id: t_Array u8 (mk_usize 32))
    : Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError =
  let n:u32 =
    cast (Std.Collections.Hash.Map.impl_1__len #u32
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #Std.Hash.Random.t_RandomState
          peers
        <:
        usize)
    <:
    u32
  in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          received
        <:
        Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
          if msg.Golden_rs.Types.f_session_id <>. session_id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err
                (ProtocolError_SessionMismatch ({ f_sender = sender_id }) <: t_ProtocolError)
                <:
                Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    match
      Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
            #FStar.Tactics.Typeclasses.solve
            received
          <:
          Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
        ()
        (fun temp_0_ temp_1_ ->
            let _:Prims.unit = temp_0_ in
            let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
            match
              Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                        u32 Golden_rs.Types.t_Ciphertext Std.Hash.Random.t_RandomState)
                    #FStar.Tactics.Typeclasses.solve
                    msg.Golden_rs.Types.f_ciphertexts
                  <:
                  Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                ()
                (fun temp_0_ temp_1_ ->
                    let _:Prims.unit = temp_0_ in
                    let (recipient_id: u32), (ct: Golden_rs.Types.t_Ciphertext) = temp_1_ in
                    let expected_share_comm:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config =
                      Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                              .Golden_rs.Types.f_vss_commitment
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
                            ct.Golden_rs.Types.f_encrypted_share
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
                                ct.Golden_rs.Types.f_r_commitment
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
                          (ProtocolError_CiphertextVerificationFailed
                            ({ f_sender = sender_id; f_recipient = recipient_id })
                            <:
                            t_ProtocolError)
                          <:
                          Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit & Prims.unit))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError
                            ) (Prims.unit & Prims.unit)) Prims.unit
                    else
                      Core_models.Ops.Control_flow.ControlFlow_Continue ()
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError
                            ) (Prims.unit & Prims.unit)) Prims.unit)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
            with
            | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break ret
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  (Prims.unit & Prims.unit))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                    (Prims.unit & Prims.unit)) Prims.unit
            | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
              let sender_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
              Ark_bls12_381_.Curves.G1.t_Config =
                peers.[ sender_id ]
              in
              match
                msg.Golden_rs.Types.f_batch_evrf_proof
                <:
                Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof
              with
              | Core_models.Option.Option_Some batch_proof ->
                let
                (peers_for_verify:
                  Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global =
                  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                        (Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
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
                            Golden_rs.Types.t_Ciphertext)
                        #FStar.Tactics.Typeclasses.solve
                        #(u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        #(u32
                            -> (u32 &
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config))
                        (Std.Collections.Hash.Map.impl_1__keys #u32
                            #Golden_rs.Types.t_Ciphertext
                            #Std.Hash.Random.t_RandomState
                            msg.Golden_rs.Types.f_ciphertexts
                          <:
                          Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
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
                        (Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
                        (u32
                            -> (u32 &
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)))
                in
                let
                (pad_commitments:
                  Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global =
                  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                        (Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                        ((u32 & Golden_rs.Types.t_Ciphertext)
                            -> (u32 &
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)))
                    #FStar.Tactics.Typeclasses.solve
                    #(Alloc.Vec.t_Vec
                        (u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                    (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter u32
                            Golden_rs.Types.t_Ciphertext)
                        #FStar.Tactics.Typeclasses.solve
                        #(u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        #((u32 & Golden_rs.Types.t_Ciphertext)
                            -> (u32 &
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config))
                        (Std.Collections.Hash.Map.impl_1__iter #u32
                            #Golden_rs.Types.t_Ciphertext
                            #Std.Hash.Random.t_RandomState
                            msg.Golden_rs.Types.f_ciphertexts
                          <:
                          Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                        (fun temp_0_ ->
                            let (pid: u32), (ct: Golden_rs.Types.t_Ciphertext) = temp_0_ in
                            pid, ct.Golden_rs.Types.f_r_commitment
                            <:
                            (u32 &
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config))
                      <:
                      Core_models.Iter.Adapters.Map.t_Map
                        (Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                        ((u32 & Golden_rs.Types.t_Ciphertext)
                            -> (u32 &
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)))
                in
                (match
                    Golden_rs.Zk_evrf.verify_evrf_batch sender_pk
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
                      beta
                      batch_proof
                    <:
                    Core_models.Result.t_Result bool Alloc.String.t_String
                  with
                  | Core_models.Result.Result_Ok true ->
                    Core_models.Ops.Control_flow.ControlFlow_Continue ()
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit & Prims.unit)) Prims.unit
                  | _ ->
                    let interest:Tracing_core.Subscriber.t_Interest =
                      Tracing_core.Callsite.impl_DefaultCallsite__interest round1__e_ee_CALLSITE
                    in
                    let enabled:bool =
                      Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                        #Tracing_core.Metadata.t_LevelFilter
                        #FStar.Tactics.Typeclasses.solve
                        Tracing_core.Metadata.impl_Level__WARN
                        Tracing.Level_filters.v_STATIC_MAX_LEVEL &&
                      Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                        #Tracing_core.Metadata.t_LevelFilter
                        #FStar.Tactics.Typeclasses.solve
                        Tracing_core.Metadata.impl_Level__WARN
                        (Tracing_core.Metadata.impl_LevelFilter__current ()
                          <:
                          Tracing_core.Metadata.t_LevelFilter) &&
                      (~.(Tracing_core.Subscriber.impl_Interest__is_never interest <: bool) &&
                      Tracing.__macro_support.e_ee_is_enabled (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                            #FStar.Tactics.Typeclasses.solve
                            round1__e_ee_CALLSITE
                          <:
                          Tracing_core.Metadata.t_Metadata)
                        interest)
                    in
                    let _:Prims.unit =
                      if enabled
                      then
                        let args:u32 = sender_id <: u32 in
                        let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                          let list = [Core_models.Fmt.Rt.impl__new_display #u32 args] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list
                        in
                        let _:Prims.unit =
                          Core_models.Ops.Function.f_call #(Tracing_core.Field.t_ValueSet
                                -> Prims.unit)
                            #Tracing_core.Field.t_ValueSet
                            #FStar.Tactics.Typeclasses.solve
                            (fun value_set ->
                                let value_set:Tracing_core.Field.t_ValueSet = value_set in
                                let meta:Tracing_core.Metadata.t_Metadata =
                                  Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                    #FStar.Tactics.Typeclasses.solve
                                    round1__e_ee_CALLSITE
                                in
                                let _:Prims.unit =
                                  Tracing_core.Event.impl__dispatch meta value_set
                                in
                                ())
                            ((Tracing_core.Field.impl_FieldSet__value_set_all (Tracing_core.Metadata.impl__fields
                                      (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                          #FStar.Tactics.Typeclasses.solve
                                          round1__e_ee_CALLSITE
                                        <:
                                        Tracing_core.Metadata.t_Metadata)
                                    <:
                                    Tracing_core.Field.t_FieldSet)
                                  ((let list =
                                        [
                                          Core_models.Option.Option_Some
                                          (Rust_primitives.unsize (Rust_primitives.unsize (Core_models.Fmt.Rt.impl_1__new_v1
                                                      (mk_usize 1)
                                                      (mk_usize 1)
                                                      (let list =
                                                          [
                                                            "Batch eVRF proof verification failed for sender="
                                                          ]
                                                        in
                                                        FStar.Pervasives.assert_norm
                                                        (Prims.eq2 (List.Tot.length list) 1);
                                                        Rust_primitives.Hax.array_of_list 1 list)
                                                      args
                                                    <:
                                                    Core_models.Fmt.t_Arguments)
                                                <:
                                                dyn 1 (fun z -> Tracing_core.Field.t_Value z)))
                                          <:
                                          Core_models.Option.t_Option
                                          (dyn 1 (fun z -> Tracing_core.Field.t_Value z))
                                        ]
                                      in
                                      FStar.Pervasives.assert_norm
                                      (Prims.eq2 (List.Tot.length list) 1);
                                      Rust_primitives.Hax.array_of_list 1 list)
                                    <:
                                    t_Slice
                                    (Core_models.Option.t_Option
                                      (dyn 1 (fun z -> Tracing_core.Field.t_Value z))))
                                <:
                                Tracing_core.Field.t_ValueSet)
                              <:
                              Tracing_core.Field.t_ValueSet)
                        in
                        ()
                    in
                    Core_models.Ops.Control_flow.ControlFlow_Continue ()
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit & Prims.unit)) Prims.unit)
              | _ ->
                Core_models.Ops.Control_flow.ControlFlow_Continue
                (Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter
                        #(Std.Collections.Hash.Map.t_HashMap u32
                            Golden_rs.Zk_evrf.t_EVRFProof
                            Std.Hash.Random.t_RandomState)
                        #FStar.Tactics.Typeclasses.solve
                        msg.Golden_rs.Types.f_evrf_proofs
                      <:
                      Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Zk_evrf.t_EVRFProof)
                    ()
                    (fun temp_0_ temp_1_ ->
                        let _:Prims.unit = temp_0_ in
                        let (recipient_id: u32), (proof: Golden_rs.Zk_evrf.t_EVRFProof) = temp_1_ in
                        let recipient_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config =
                          peers.[ recipient_id ]
                        in
                        let r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config =
                          (msg.Golden_rs.Types.f_ciphertexts.[ recipient_id ])
                            .Golden_rs.Types.f_r_commitment
                        in
                        match
                          Golden_rs.Zk_evrf.verify_evrf sender_pk
                            recipient_pk
                            r_commitment
                            beta
                            proof
                          <:
                          Core_models.Result.t_Result bool Alloc.String.t_String
                        with
                        | Core_models.Result.Result_Ok true -> ()
                        | _ ->
                          let interest:Tracing_core.Subscriber.t_Interest =
                            Tracing_core.Callsite.impl_DefaultCallsite__interest round1__e_ee_CALLSITE_1

                          in
                          let enabled:bool =
                            Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                              #Tracing_core.Metadata.t_LevelFilter
                              #FStar.Tactics.Typeclasses.solve
                              Tracing_core.Metadata.impl_Level__WARN
                              Tracing.Level_filters.v_STATIC_MAX_LEVEL &&
                            Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                              #Tracing_core.Metadata.t_LevelFilter
                              #FStar.Tactics.Typeclasses.solve
                              Tracing_core.Metadata.impl_Level__WARN
                              (Tracing_core.Metadata.impl_LevelFilter__current ()
                                <:
                                Tracing_core.Metadata.t_LevelFilter) &&
                            (~.(Tracing_core.Subscriber.impl_Interest__is_never interest <: bool) &&
                            Tracing.__macro_support.e_ee_is_enabled (Tracing_core.Callsite.f_metadata
                                  #Tracing_core.Callsite.t_DefaultCallsite
                                  #FStar.Tactics.Typeclasses.solve
                                  round1__e_ee_CALLSITE_1
                                <:
                                Tracing_core.Metadata.t_Metadata)
                              interest)
                          in
                          let _:Prims.unit =
                            if enabled
                            then
                              let args:(u32 & u32) = sender_id, recipient_id <: (u32 & u32) in
                              let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 2) =
                                let list =
                                  [
                                    Core_models.Fmt.Rt.impl__new_display #u32 args._1;
                                    Core_models.Fmt.Rt.impl__new_display #u32 args._2
                                  ]
                                in
                                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                                Rust_primitives.Hax.array_of_list 2 list
                              in
                              let _:Prims.unit =
                                Core_models.Ops.Function.f_call #(Tracing_core.Field.t_ValueSet
                                      -> Prims.unit)
                                  #Tracing_core.Field.t_ValueSet
                                  #FStar.Tactics.Typeclasses.solve
                                  (fun value_set ->
                                      let value_set:Tracing_core.Field.t_ValueSet = value_set in
                                      let meta:Tracing_core.Metadata.t_Metadata =
                                        Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                          #FStar.Tactics.Typeclasses.solve
                                          round1__e_ee_CALLSITE_1
                                      in
                                      let _:Prims.unit =
                                        Tracing_core.Event.impl__dispatch meta value_set
                                      in
                                      ())
                                  ((Tracing_core.Field.impl_FieldSet__value_set_all (Tracing_core.Metadata.impl__fields
                                            (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                                #FStar.Tactics.Typeclasses.solve
                                                round1__e_ee_CALLSITE_1
                                              <:
                                              Tracing_core.Metadata.t_Metadata)
                                          <:
                                          Tracing_core.Field.t_FieldSet)
                                        ((let list =
                                              [
                                                Core_models.Option.Option_Some
                                                (Rust_primitives.unsize (Rust_primitives.unsize (Core_models.Fmt.Rt.impl_1__new_v1
                                                            (mk_usize 2)
                                                            (mk_usize 2)
                                                            (let list =
                                                                [
                                                                  "eVRF proof verification failed for sender=";
                                                                  " recipient="
                                                                ]
                                                              in
                                                              FStar.Pervasives.assert_norm
                                                              (Prims.eq2 (List.Tot.length list) 2);
                                                              Rust_primitives.Hax.array_of_list 2
                                                                list)
                                                            args
                                                          <:
                                                          Core_models.Fmt.t_Arguments)
                                                      <:
                                                      dyn 1 (fun z -> Tracing_core.Field.t_Value z))
                                                )
                                                <:
                                                Core_models.Option.t_Option
                                                (dyn 1 (fun z -> Tracing_core.Field.t_Value z))
                                              ]
                                            in
                                            FStar.Pervasives.assert_norm
                                            (Prims.eq2 (List.Tot.length list) 1);
                                            Rust_primitives.Hax.array_of_list 1 list)
                                          <:
                                          t_Slice
                                          (Core_models.Option.t_Option
                                            (dyn 1 (fun z -> Tracing_core.Field.t_Value z))))
                                      <:
                                      Tracing_core.Field.t_ValueSet)
                                    <:
                                    Tracing_core.Field.t_ValueSet)
                              in
                              ()
                          in
                          ()))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit & Prims.unit)) Prims.unit)
      <:
      Core_models.Ops.Control_flow.t_ControlFlow
        (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
      let secret_share:Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
        own_share
      in
      match
        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                  u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
              #FStar.Tactics.Typeclasses.solve
              received
            <:
            Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
          secret_share
          (fun secret_share temp_1_ ->
              let secret_share:Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                secret_share
              in
              let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
              match
                Core_models.Option.impl__ok_or #Golden_rs.Types.t_Ciphertext
                  #t_ProtocolError
                  (Std.Collections.Hash.Map.impl_2__get #u32
                      #Golden_rs.Types.t_Ciphertext
                      #Std.Hash.Random.t_RandomState
                      #u32
                      msg.Golden_rs.Types.f_ciphertexts
                      id
                    <:
                    Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext)
                  (ProtocolError_MissingCiphertext ({ f_sender = sender_id; f_recipient = id })
                    <:
                    t_ProtocolError)
                <:
                Core_models.Result.t_Result Golden_rs.Types.t_Ciphertext t_ProtocolError
              with
              | Core_models.Result.Result_Ok ct ->
                let sender_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config =
                  peers.[ sender_id ]
                in
                let
                (r_pad:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                (_:
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                =
                  Golden_rs.Evrf.derive_pad sk
                    sender_pk
                    (msg.Golden_rs.Types.f_random_msg <: t_Slice u8)
                    beta
                in
                let decrypted_share:Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                  Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #FStar.Tactics.Typeclasses.solve
                    ct.Golden_rs.Types.f_encrypted_share
                    r_pad
                in
                let secret_share:Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                  Core_models.Ops.Arith.f_add_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #FStar.Tactics.Typeclasses.solve
                    secret_share
                    decrypted_share
                in
                Core_models.Ops.Control_flow.ControlFlow_Continue secret_share
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit &
                        Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                    (Prims.unit &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit &
                        Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue secret_share ->
        let pk_projective:Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config =
          Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
              Ark_bls12_381_.Curves.G1.t_Config)
            #FStar.Tactics.Typeclasses.solve
            (own_vss_commitment.[ mk_usize 0 ]
              <:
              Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        in
        let pk_projective:Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config =
          Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_Values
                    u32 Golden_rs.Types.t_Round0Msg)
                #FStar.Tactics.Typeclasses.solve
                (Std.Collections.Hash.Map.impl_1__values #u32
                    #Golden_rs.Types.t_Round0Msg
                    #Std.Hash.Random.t_RandomState
                    received
                  <:
                  Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
              <:
              Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
            pk_projective
            (fun pk_projective msg ->
                let pk_projective:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config =
                  pk_projective
                in
                let msg:Golden_rs.Types.t_Round0Msg = msg in
                Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #FStar.Tactics.Typeclasses.solve
                  pk_projective
                  (msg.Golden_rs.Types.f_vss_commitment.[ mk_usize 0 ]
                    <:
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
            )
        in
        let public_key:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config =
          Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
              Ark_bls12_381_.Curves.G1.t_Config)
            #FStar.Tactics.Typeclasses.solve
            pk_projective
        in
        let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Std.Hash.Random.t_RandomState =
          Std.Collections.Hash.Map.impl__new #u32
            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            ()
        in
        let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Std.Hash.Random.t_RandomState =
          Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Core_models.Ops.Range.t_RangeInclusive
                  u32)
                #FStar.Tactics.Typeclasses.solve
                (Core_models.Ops.Range.impl_7__new #u32 (mk_u32 1) n
                  <:
                  Core_models.Ops.Range.t_RangeInclusive u32)
              <:
              Core_models.Ops.Range.t_RangeInclusive u32)
            public_key_shares
            (fun public_key_shares k ->
                let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  )
                  Std.Hash.Random.t_RandomState =
                  public_key_shares
                in
                let k:u32 = k in
                let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config =
                  Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                    #FStar.Tactics.Typeclasses.solve
                    (Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice own_vss_commitment

                          <:
                          t_Slice
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                        k
                      <:
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                in
                let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config =
                  Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter
                        #(Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                        #FStar.Tactics.Typeclasses.solve
                        (Std.Collections.Hash.Map.impl_1__values #u32
                            #Golden_rs.Types.t_Round0Msg
                            #Std.Hash.Random.t_RandomState
                            received
                          <:
                          Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                      <:
                      Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                    pk_k
                    (fun pk_k msg ->
                        let pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config =
                          pk_k
                        in
                        let msg:Golden_rs.Types.t_Round0Msg = msg in
                        Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                            Ark_bls12_381_.Curves.G1.t_Config)
                          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)
                          #FStar.Tactics.Typeclasses.solve
                          pk_k
                          (Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                                    .Golden_rs.Types.f_vss_commitment
                                <:
                                t_Slice
                                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config))
                              k
                            <:
                            Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config)
                        <:
                        Ark_ec.Models.Short_weierstrass.Group.t_Projective
                        Ark_bls12_381_.Curves.G1.t_Config)
                in
                let
                (tmp0:
                  Std.Collections.Hash.Map.t_HashMap u32
                    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                    Std.Hash.Random.t_RandomState),
                (out:
                  Core_models.Option.t_Option
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  )) =
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
                  (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
                  )
                  Std.Hash.Random.t_RandomState =
                  tmp0
                in
                let _:Core_models.Option.t_Option
                (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                =
                  out
                in
                public_key_shares)
        in
        Core_models.Result.Result_Ok
        ({
            Golden_rs.Types.f_public_key = public_key;
            Golden_rs.Types.f_public_key_shares = public_key_shares;
            Golden_rs.Types.f_secret_share = secret_share
          }
          <:
          Golden_rs.Types.t_DkgOutput)
        <:
        Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError

/// Execute Round 1 for key refresh (zero secret sharing).
/// Per Section 5.2 of the Golden paper (IACR 2025/1924):
/// > "Check that A_{j,0} equals the group identity for all j (verifying f_j(0) = 0)"
/// Identical to [`round1`] but with an additional check that `A_{j,0} == identity`
/// for all senders. The output `secret_share = existing_share + sum of zero-sharing
/// deltas`. The output `public_key` is carried forward from the original DKG (unchanged).
let round1_refresh
      (id: u32)
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (peers:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (own_refresh_delta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (own_vss_commitment:
          Alloc.Vec.t_Vec
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Alloc.Alloc.t_Global)
      (received:
          Std.Collections.Hash.Map.t_HashMap u32
            Golden_rs.Types.t_Round0Msg
            Std.Hash.Random.t_RandomState)
      (beta existing_share:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (original_pk:
          Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (original_pk_shares:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState)
      (session_id: t_Array u8 (mk_usize 32))
    : Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError =
  let n:u32 =
    cast (Std.Collections.Hash.Map.impl_1__len #u32
          #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          #Std.Hash.Random.t_RandomState
          peers
        <:
        usize)
    <:
    u32
  in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
              u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
          #FStar.Tactics.Typeclasses.solve
          received
        <:
        Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
          if msg.Golden_rs.Types.f_session_id <>. session_id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err
                (ProtocolError_SessionMismatch ({ f_sender = sender_id }) <: t_ProtocolError)
                <:
                Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    if
      ~.(own_vss_commitment.[ mk_usize 0 ]
        <:
        Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
    then
      Core_models.Result.Result_Err
      (ProtocolError_ZeroSecretViolation ({ f_sender = id }) <: t_ProtocolError)
      <:
      Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError
    else
      match
        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                  u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
              #FStar.Tactics.Typeclasses.solve
              received
            <:
            Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
          ()
          (fun temp_0_ temp_1_ ->
              let _:Prims.unit = temp_0_ in
              let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
              if
                ~.(msg.Golden_rs.Types.f_vss_commitment.[ mk_usize 0 ]
                  <:
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                  .Ark_ec.Models.Short_weierstrass.Affine.f_infinity
                <:
                bool
              then
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err
                    (ProtocolError_ZeroSecretViolation ({ f_sender = sender_id }) <: t_ProtocolError
                    )
                    <:
                    Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                    (Prims.unit & Prims.unit))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit & Prims.unit)) Prims.unit
              else
                Core_models.Ops.Control_flow.ControlFlow_Continue ()
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit & Prims.unit)) Prims.unit)
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
        match
          Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                    u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
                #FStar.Tactics.Typeclasses.solve
                received
              <:
              Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
            ()
            (fun temp_0_ temp_1_ ->
                let _:Prims.unit = temp_0_ in
                let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
                match
                  Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                        #(Std.Collections.Hash.Map.t_HashMap u32
                            Golden_rs.Types.t_Ciphertext
                            Std.Hash.Random.t_RandomState)
                        #FStar.Tactics.Typeclasses.solve
                        msg.Golden_rs.Types.f_ciphertexts
                      <:
                      Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                    ()
                    (fun temp_0_ temp_1_ ->
                        let _:Prims.unit = temp_0_ in
                        let (recipient_id: u32), (ct: Golden_rs.Types.t_Ciphertext) = temp_1_ in
                        let expected_share_comm:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config =
                          Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                                  .Golden_rs.Types.f_vss_commitment
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
                                ct.Golden_rs.Types.f_encrypted_share
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
                                    ct.Golden_rs.Types.f_r_commitment
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
                              (ProtocolError_CiphertextVerificationFailed
                                ({ f_sender = sender_id; f_recipient = recipient_id })
                                <:
                                t_ProtocolError)
                              <:
                              Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                t_ProtocolError)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                  t_ProtocolError) (Prims.unit & Prims.unit))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                    t_ProtocolError) (Prims.unit & Prims.unit)) Prims.unit
                        else
                          Core_models.Ops.Control_flow.ControlFlow_Continue ()
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                    t_ProtocolError) (Prims.unit & Prims.unit)) Prims.unit)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                    Prims.unit
                with
                | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break ret
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      (Prims.unit & Prims.unit))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                        (Prims.unit & Prims.unit)) Prims.unit
                | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                  let sender_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                  Ark_bls12_381_.Curves.G1.t_Config =
                    peers.[ sender_id ]
                  in
                  match
                    msg.Golden_rs.Types.f_batch_evrf_proof
                    <:
                    Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof
                  with
                  | Core_models.Option.Option_Some batch_proof ->
                    let
                    (peers_for_verify:
                      Alloc.Vec.t_Vec
                        (u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                      (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global =
                      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                            (Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
                            (u32
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)))
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec
                            (u32 &
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                        (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Keys
                                u32 Golden_rs.Types.t_Ciphertext)
                            #FStar.Tactics.Typeclasses.solve
                            #(u32 &
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)
                            #(u32
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config))
                            (Std.Collections.Hash.Map.impl_1__keys #u32
                                #Golden_rs.Types.t_Ciphertext
                                #Std.Hash.Random.t_RandomState
                                msg.Golden_rs.Types.f_ciphertexts
                              <:
                              Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
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
                            (Std.Collections.Hash.Map.t_Keys u32 Golden_rs.Types.t_Ciphertext)
                            (u32
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)))
                    in
                    let
                    (pad_commitments:
                      Alloc.Vec.t_Vec
                        (u32 &
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                      (u32 &
                        Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global =
                      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                            (Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                            ((u32 & Golden_rs.Types.t_Ciphertext)
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)))
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec
                            (u32 &
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                        (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter
                                u32 Golden_rs.Types.t_Ciphertext)
                            #FStar.Tactics.Typeclasses.solve
                            #(u32 &
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)
                            #((u32 & Golden_rs.Types.t_Ciphertext)
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config))
                            (Std.Collections.Hash.Map.impl_1__iter #u32
                                #Golden_rs.Types.t_Ciphertext
                                #Std.Hash.Random.t_RandomState
                                msg.Golden_rs.Types.f_ciphertexts
                              <:
                              Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                            (fun temp_0_ ->
                                let (pid: u32), (ct: Golden_rs.Types.t_Ciphertext) = temp_0_ in
                                pid, ct.Golden_rs.Types.f_r_commitment
                                <:
                                (u32 &
                                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config))
                          <:
                          Core_models.Iter.Adapters.Map.t_Map
                            (Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Ciphertext)
                            ((u32 & Golden_rs.Types.t_Ciphertext)
                                -> (u32 &
                                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)))
                    in
                    (match
                        Golden_rs.Zk_evrf.verify_evrf_batch sender_pk
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
                          beta
                          batch_proof
                        <:
                        Core_models.Result.t_Result bool Alloc.String.t_String
                      with
                      | Core_models.Result.Result_Ok true ->
                        Core_models.Ops.Control_flow.ControlFlow_Continue ()
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                  t_ProtocolError) (Prims.unit & Prims.unit)) Prims.unit
                      | _ ->
                        let interest:Tracing_core.Subscriber.t_Interest =
                          Tracing_core.Callsite.impl_DefaultCallsite__interest round1_refresh__e_ee_CALLSITE

                        in
                        let enabled:bool =
                          Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                            #Tracing_core.Metadata.t_LevelFilter
                            #FStar.Tactics.Typeclasses.solve
                            Tracing_core.Metadata.impl_Level__WARN
                            Tracing.Level_filters.v_STATIC_MAX_LEVEL &&
                          Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                            #Tracing_core.Metadata.t_LevelFilter
                            #FStar.Tactics.Typeclasses.solve
                            Tracing_core.Metadata.impl_Level__WARN
                            (Tracing_core.Metadata.impl_LevelFilter__current ()
                              <:
                              Tracing_core.Metadata.t_LevelFilter) &&
                          (~.(Tracing_core.Subscriber.impl_Interest__is_never interest <: bool) &&
                          Tracing.__macro_support.e_ee_is_enabled (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                #FStar.Tactics.Typeclasses.solve
                                round1_refresh__e_ee_CALLSITE
                              <:
                              Tracing_core.Metadata.t_Metadata)
                            interest)
                        in
                        let _:Prims.unit =
                          if enabled
                          then
                            let args:u32 = sender_id <: u32 in
                            let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                              let list = [Core_models.Fmt.Rt.impl__new_display #u32 args] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list
                            in
                            let _:Prims.unit =
                              Core_models.Ops.Function.f_call #(Tracing_core.Field.t_ValueSet
                                    -> Prims.unit)
                                #Tracing_core.Field.t_ValueSet
                                #FStar.Tactics.Typeclasses.solve
                                (fun value_set ->
                                    let value_set:Tracing_core.Field.t_ValueSet = value_set in
                                    let meta:Tracing_core.Metadata.t_Metadata =
                                      Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                        #FStar.Tactics.Typeclasses.solve
                                        round1_refresh__e_ee_CALLSITE
                                    in
                                    let _:Prims.unit =
                                      Tracing_core.Event.impl__dispatch meta value_set
                                    in
                                    ())
                                ((Tracing_core.Field.impl_FieldSet__value_set_all (Tracing_core.Metadata.impl__fields
                                          (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                              #FStar.Tactics.Typeclasses.solve
                                              round1_refresh__e_ee_CALLSITE
                                            <:
                                            Tracing_core.Metadata.t_Metadata)
                                        <:
                                        Tracing_core.Field.t_FieldSet)
                                      ((let list =
                                            [
                                              Core_models.Option.Option_Some
                                              (Rust_primitives.unsize (Rust_primitives.unsize (Core_models.Fmt.Rt.impl_1__new_v1
                                                          (mk_usize 1)
                                                          (mk_usize 1)
                                                          (let list =
                                                              [
                                                                "Batch eVRF proof verification failed for sender="
                                                              ]
                                                            in
                                                            FStar.Pervasives.assert_norm
                                                            (Prims.eq2 (List.Tot.length list) 1);
                                                            Rust_primitives.Hax.array_of_list 1 list
                                                          )
                                                          args
                                                        <:
                                                        Core_models.Fmt.t_Arguments)
                                                    <:
                                                    dyn 1 (fun z -> Tracing_core.Field.t_Value z)))
                                              <:
                                              Core_models.Option.t_Option
                                              (dyn 1 (fun z -> Tracing_core.Field.t_Value z))
                                            ]
                                          in
                                          FStar.Pervasives.assert_norm
                                          (Prims.eq2 (List.Tot.length list) 1);
                                          Rust_primitives.Hax.array_of_list 1 list)
                                        <:
                                        t_Slice
                                        (Core_models.Option.t_Option
                                          (dyn 1 (fun z -> Tracing_core.Field.t_Value z))))
                                    <:
                                    Tracing_core.Field.t_ValueSet)
                                  <:
                                  Tracing_core.Field.t_ValueSet)
                            in
                            ()
                        in
                        Core_models.Ops.Control_flow.ControlFlow_Continue ()
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput
                                  t_ProtocolError) (Prims.unit & Prims.unit)) Prims.unit)
                  | _ ->
                    Core_models.Ops.Control_flow.ControlFlow_Continue
                    (Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter
                            #(Std.Collections.Hash.Map.t_HashMap u32
                                Golden_rs.Zk_evrf.t_EVRFProof
                                Std.Hash.Random.t_RandomState)
                            #FStar.Tactics.Typeclasses.solve
                            msg.Golden_rs.Types.f_evrf_proofs
                          <:
                          Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Zk_evrf.t_EVRFProof)
                        ()
                        (fun temp_0_ temp_1_ ->
                            let _:Prims.unit = temp_0_ in
                            let (recipient_id: u32), (proof: Golden_rs.Zk_evrf.t_EVRFProof) =
                              temp_1_
                            in
                            let recipient_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config =
                              peers.[ recipient_id ]
                            in
                            let r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config =
                              (msg.Golden_rs.Types.f_ciphertexts.[ recipient_id ])
                                .Golden_rs.Types.f_r_commitment
                            in
                            match
                              Golden_rs.Zk_evrf.verify_evrf sender_pk
                                recipient_pk
                                r_commitment
                                beta
                                proof
                              <:
                              Core_models.Result.t_Result bool Alloc.String.t_String
                            with
                            | Core_models.Result.Result_Ok true -> ()
                            | _ ->
                              let interest:Tracing_core.Subscriber.t_Interest =
                                Tracing_core.Callsite.impl_DefaultCallsite__interest round1_refresh__e_ee_CALLSITE_1

                              in
                              let enabled:bool =
                                Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                                  #Tracing_core.Metadata.t_LevelFilter
                                  #FStar.Tactics.Typeclasses.solve
                                  Tracing_core.Metadata.impl_Level__WARN
                                  Tracing.Level_filters.v_STATIC_MAX_LEVEL &&
                                Core_models.Cmp.f_le #Tracing_core.Metadata.t_Level
                                  #Tracing_core.Metadata.t_LevelFilter
                                  #FStar.Tactics.Typeclasses.solve
                                  Tracing_core.Metadata.impl_Level__WARN
                                  (Tracing_core.Metadata.impl_LevelFilter__current ()
                                    <:
                                    Tracing_core.Metadata.t_LevelFilter) &&
                                (~.(Tracing_core.Subscriber.impl_Interest__is_never interest <: bool
                                ) &&
                                Tracing.__macro_support.e_ee_is_enabled (Tracing_core.Callsite.f_metadata
                                      #Tracing_core.Callsite.t_DefaultCallsite
                                      #FStar.Tactics.Typeclasses.solve
                                      round1_refresh__e_ee_CALLSITE_1
                                    <:
                                    Tracing_core.Metadata.t_Metadata)
                                  interest)
                              in
                              let _:Prims.unit =
                                if enabled
                                then
                                  let args:(u32 & u32) = sender_id, recipient_id <: (u32 & u32) in
                                  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 2) =
                                    let list =
                                      [
                                        Core_models.Fmt.Rt.impl__new_display #u32 args._1;
                                        Core_models.Fmt.Rt.impl__new_display #u32 args._2
                                      ]
                                    in
                                    FStar.Pervasives.assert_norm
                                    (Prims.eq2 (List.Tot.length list) 2);
                                    Rust_primitives.Hax.array_of_list 2 list
                                  in
                                  let _:Prims.unit =
                                    Core_models.Ops.Function.f_call #(Tracing_core.Field.t_ValueSet
                                          -> Prims.unit)
                                      #Tracing_core.Field.t_ValueSet
                                      #FStar.Tactics.Typeclasses.solve
                                      (fun value_set ->
                                          let value_set:Tracing_core.Field.t_ValueSet = value_set in
                                          let meta:Tracing_core.Metadata.t_Metadata =
                                            Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                              #FStar.Tactics.Typeclasses.solve
                                              round1_refresh__e_ee_CALLSITE_1
                                          in
                                          let _:Prims.unit =
                                            Tracing_core.Event.impl__dispatch meta value_set
                                          in
                                          ())
                                      ((Tracing_core.Field.impl_FieldSet__value_set_all (Tracing_core.Metadata.impl__fields
                                                (Tracing_core.Callsite.f_metadata #Tracing_core.Callsite.t_DefaultCallsite
                                                    #FStar.Tactics.Typeclasses.solve
                                                    round1_refresh__e_ee_CALLSITE_1
                                                  <:
                                                  Tracing_core.Metadata.t_Metadata)
                                              <:
                                              Tracing_core.Field.t_FieldSet)
                                            ((let list =
                                                  [
                                                    Core_models.Option.Option_Some
                                                    (Rust_primitives.unsize (Rust_primitives.unsize (
                                                              Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize
                                                                  2)
                                                                (mk_usize 2)
                                                                (let list =
                                                                    [
                                                                      "eVRF proof verification failed for sender=";
                                                                      " recipient="
                                                                    ]
                                                                  in
                                                                  FStar.Pervasives.assert_norm
                                                                  (Prims.eq2 (List.Tot.length list)
                                                                      2);
                                                                  Rust_primitives.Hax.array_of_list
                                                                    2 list)
                                                                args
                                                              <:
                                                              Core_models.Fmt.t_Arguments)
                                                          <:
                                                          dyn 1
                                                            (fun z -> Tracing_core.Field.t_Value z))
                                                    )
                                                    <:
                                                    Core_models.Option.t_Option
                                                    (dyn 1 (fun z -> Tracing_core.Field.t_Value z))
                                                  ]
                                                in
                                                FStar.Pervasives.assert_norm
                                                (Prims.eq2 (List.Tot.length list) 1);
                                                Rust_primitives.Hax.array_of_list 1 list)
                                              <:
                                              t_Slice
                                              (Core_models.Option.t_Option
                                                (dyn 1 (fun z -> Tracing_core.Field.t_Value z))))
                                          <:
                                          Tracing_core.Field.t_ValueSet)
                                        <:
                                        Tracing_core.Field.t_ValueSet)
                                  in
                                  ()
                              in
                              ()))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit & Prims.unit)) Prims.unit)
          <:
          Core_models.Ops.Control_flow.t_ControlFlow
            (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError) Prims.unit
        with
        | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
        | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
          let total_delta:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            own_refresh_delta
          in
          match
            Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Map.t_HashMap
                      u32 Golden_rs.Types.t_Round0Msg Std.Hash.Random.t_RandomState)
                  #FStar.Tactics.Typeclasses.solve
                  received
                <:
                Std.Collections.Hash.Map.t_Iter u32 Golden_rs.Types.t_Round0Msg)
              total_delta
              (fun total_delta temp_1_ ->
                  let total_delta:Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                    total_delta
                  in
                  let (sender_id: u32), (msg: Golden_rs.Types.t_Round0Msg) = temp_1_ in
                  match
                    Core_models.Option.impl__ok_or #Golden_rs.Types.t_Ciphertext
                      #t_ProtocolError
                      (Std.Collections.Hash.Map.impl_2__get #u32
                          #Golden_rs.Types.t_Ciphertext
                          #Std.Hash.Random.t_RandomState
                          #u32
                          msg.Golden_rs.Types.f_ciphertexts
                          id
                        <:
                        Core_models.Option.t_Option Golden_rs.Types.t_Ciphertext)
                      (ProtocolError_MissingCiphertext ({ f_sender = sender_id; f_recipient = id })
                        <:
                        t_ProtocolError)
                    <:
                    Core_models.Result.t_Result Golden_rs.Types.t_Ciphertext t_ProtocolError
                  with
                  | Core_models.Result.Result_Ok ct ->
                    let sender_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config =
                      peers.[ sender_id ]
                    in
                    let
                    (r_pad:
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                    (_:
                      Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config) =
                      Golden_rs.Evrf.derive_pad sk
                        sender_pk
                        (msg.Golden_rs.Types.f_random_msg <: t_Slice u8)
                        beta
                    in
                    let decrypted_share:Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                      Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        ct.Golden_rs.Types.f_encrypted_share
                        r_pad
                    in
                    let total_delta:Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                      Core_models.Ops.Arith.f_add_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        total_delta
                        decrypted_share
                    in
                    Core_models.Ops.Control_flow.ControlFlow_Continue total_delta
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  | Core_models.Result.Result_Err err ->
                    Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                        (Prims.unit &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
                          (Prims.unit &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError)
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          with
          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
          | Core_models.Ops.Control_flow.ControlFlow_Continue total_delta ->
            let new_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
              Core_models.Ops.Arith.f_add #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #FStar.Tactics.Typeclasses.solve
                existing_share
                total_delta
            in
            let public_key:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config =
              original_pk
            in
            let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState =
              Std.Collections.Hash.Map.impl__new #u32
                #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
                ()
            in
            let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState =
              Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(
                      Core_models.Ops.Range.t_RangeInclusive u32)
                    #FStar.Tactics.Typeclasses.solve
                    (Core_models.Ops.Range.impl_7__new #u32 (mk_u32 1) n
                      <:
                      Core_models.Ops.Range.t_RangeInclusive u32)
                  <:
                  Core_models.Ops.Range.t_RangeInclusive u32)
                public_key_shares
                (fun public_key_shares k ->
                    let public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
                      (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config)
                      Std.Hash.Random.t_RandomState =
                      public_key_shares
                    in
                    let k:u32 = k in
                    let delta_pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config =
                      Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        #FStar.Tactics.Typeclasses.solve
                        (Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice own_vss_commitment

                              <:
                              t_Slice
                              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config))
                            k
                          <:
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                    in
                    let delta_pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config =
                      Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter
                            #(Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                            #FStar.Tactics.Typeclasses.solve
                            (Std.Collections.Hash.Map.impl_1__values #u32
                                #Golden_rs.Types.t_Round0Msg
                                #Std.Hash.Random.t_RandomState
                                received
                              <:
                              Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                          <:
                          Std.Collections.Hash.Map.t_Values u32 Golden_rs.Types.t_Round0Msg)
                        delta_pk_k
                        (fun delta_pk_k msg ->
                            let delta_pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                            Ark_bls12_381_.Curves.G1.t_Config =
                              delta_pk_k
                            in
                            let msg:Golden_rs.Types.t_Round0Msg = msg in
                            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                Ark_bls12_381_.Curves.G1.t_Config)
                              #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                              #FStar.Tactics.Typeclasses.solve
                              delta_pk_k
                              (Golden_rs.Vss.expected_share_commitment (Alloc.Vec.impl_1__as_slice msg
                                        .Golden_rs.Types.f_vss_commitment
                                    <:
                                    t_Slice
                                    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                      Ark_bls12_381_.Curves.G1.t_Config))
                                  k
                                <:
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                            <:
                            Ark_ec.Models.Short_weierstrass.Group.t_Projective
                            Ark_bls12_381_.Curves.G1.t_Config)
                    in
                    let original_pk_k:Ark_ec.Models.Short_weierstrass.Group.t_Projective
                    Ark_bls12_381_.Curves.G1.t_Config =
                      Ark_ec.f_into_group #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                        #FStar.Tactics.Typeclasses.solve
                        (original_pk_shares.[ k ]
                          <:
                          Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config)
                    in
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
                            (Core_models.Ops.Arith.f_add #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                  Ark_bls12_381_.Curves.G1.t_Config)
                                #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                                  Ark_bls12_381_.Curves.G1.t_Config)
                                #FStar.Tactics.Typeclasses.solve
                                original_pk_k
                                delta_pk_k
                              <:
                              Ark_ec.Models.Short_weierstrass.Group.t_Projective
                              Ark_bls12_381_.Curves.G1.t_Config)
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
                    public_key_shares)
            in
            Core_models.Result.Result_Ok
            ({
                Golden_rs.Types.f_public_key = public_key;
                Golden_rs.Types.f_public_key_shares = public_key_shares;
                Golden_rs.Types.f_secret_share = new_secret_share
              }
              <:
              Golden_rs.Types.t_DkgOutput)
            <:
            Core_models.Result.t_Result Golden_rs.Types.t_DkgOutput t_ProtocolError
