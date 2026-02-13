module Golden_rs.Network
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Golden_rs.Types in
  let open Rand_core in
  let open Rand_core.Os in
  ()

/// Simulated broadcast channel with peer discovery.
/// Per Section 5.1 of the Golden paper (IACR 2025/1924):
/// > "Each party i maintains (sk_i^I, PK_i^I) where PK_i^I = g^{sk_i^I} in G_in."
/// All nodes register their identity public key, then use a shared broadcast
/// channel to send Round 0 messages to every other participant.
type t_Network = {
  f_sender:Tokio.Sync.Broadcast.t_Sender Golden_rs.Types.t_Round0Msg;
  f_peers:Alloc.Sync.t_Arc
    (Tokio.Sync.Rwlock.t_RwLock
      (Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Std.Hash.Random.t_RandomState)) Alloc.Alloc.t_Global;
  f_barrier:Alloc.Sync.t_Arc Tokio.Sync.Barrier.t_Barrier Alloc.Alloc.t_Global;
  f_session_id:Alloc.Sync.t_Arc (t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global
}

let impl_1: Core_models.Clone.t_Clone t_Network =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

/// Create a new network for `n` participants.
/// The broadcast channel capacity is `n * 2` to avoid dropped messages.
let impl_Network__new (n: u32) : t_Network =
  let
  (sender: Tokio.Sync.Broadcast.t_Sender Golden_rs.Types.t_Round0Msg),
  (_: Tokio.Sync.Broadcast.t_Receiver Golden_rs.Types.t_Round0Msg) =
    Tokio.Sync.Broadcast.channel #Golden_rs.Types.t_Round0Msg (cast (n *! mk_u32 2 <: u32) <: usize)
  in
  let session_id:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let session_id:t_Array u8 (mk_usize 32) =
    Rand_core.f_fill_bytes #Rand_core.Os.t_OsRng
      #FStar.Tactics.Typeclasses.solve
      (Rand_core.Os.OsRng <: Rand_core.Os.t_OsRng)
      session_id
  in
  {
    f_sender = sender;
    f_peers
    =
    Alloc.Sync.impl_16__new #(Tokio.Sync.Rwlock.t_RwLock
        (Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState))
      (Tokio.Sync.Rwlock.impl_14__new #(Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState)
          (Std.Collections.Hash.Map.impl__new #u32
              #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              ()
            <:
            Std.Collections.Hash.Map.t_HashMap u32
              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
              Std.Hash.Random.t_RandomState)
        <:
        Tokio.Sync.Rwlock.t_RwLock
        (Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
            Std.Hash.Random.t_RandomState));
    f_barrier
    =
    Alloc.Sync.impl_16__new #Tokio.Sync.Barrier.t_Barrier
      (Tokio.Sync.Barrier.impl_Barrier__new (cast (n <: u32) <: usize)
        <:
        Tokio.Sync.Barrier.t_Barrier);
    f_session_id = Alloc.Sync.impl_16__new #(t_Array u8 (mk_usize 32)) session_id
  }
  <:
  t_Network

/// Get the session ID for this network session.
let impl_Network__session_id (self: t_Network) : t_Array u8 (mk_usize 32) =
  Core_models.Ops.Deref.f_deref #(Alloc.Sync.t_Arc (t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global)
    #FStar.Tactics.Typeclasses.solve
    self.f_session_id

/// Register a node's identity public key with proof of knowledge.
/// Per Appendix F of the Golden paper (IACR 2025/1924), registration
/// requires proving knowledge of the secret key to prevent rogue-key attacks.
/// Returns a broadcast receiver on success, or an error if the Schnorr PoK
/// is invalid.
let impl_Network__register
      (self: t_Network)
      (id: u32)
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (pok: Golden_rs.Schnorr_pok.t_SchnorrPoK)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Wait for all nodes to finish registration.
/// Blocks until all `n` participants have registered, ensuring the peer
/// directory is complete before Round 0 begins.
let impl_Network__wait_ready (self: t_Network) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Broadcast a Round 0 message to all participants.
/// Sends the message on the shared broadcast channel. All registered
/// receivers will obtain a copy.
let impl_Network__broadcast (self: t_Network) (msg: Golden_rs.Types.t_Round0Msg) : Prims.unit =
  let _:Core_models.Result.t_Result usize
    (Tokio.Sync.Broadcast.Error.t_SendError Golden_rs.Types.t_Round0Msg) =
    Tokio.Sync.Broadcast.impl_3__send #Golden_rs.Types.t_Round0Msg self.f_sender msg
  in
  ()

/// Get a snapshot of all registered peer public keys.
/// Returns a clone of the current peer directory mapping `NodeId` to
/// identity public key.
let impl_Network__get_peers (self: t_Network) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""
