module Golden_rs.Reshare_network
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

/// Network for the resharing protocol with two groups: old members broadcast,
/// new members receive.
/// Maintains separate registries for old-group and new-group identity keys,
/// and a shared broadcast channel for reshare messages.
type t_ReshareNetwork = {
  f_sender:Tokio.Sync.Broadcast.t_Sender Golden_rs.Types.t_ReshareMsg;
  f_old_members:Alloc.Sync.t_Arc
    (Tokio.Sync.Rwlock.t_RwLock
      (Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Std.Hash.Random.t_RandomState)) Alloc.Alloc.t_Global;
  f_new_members:Alloc.Sync.t_Arc
    (Tokio.Sync.Rwlock.t_RwLock
      (Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          Std.Hash.Random.t_RandomState)) Alloc.Alloc.t_Global;
  f_barrier:Alloc.Sync.t_Arc Tokio.Sync.Barrier.t_Barrier Alloc.Alloc.t_Global;
  f_session_id:Alloc.Sync.t_Arc (t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global
}

let impl_1: Core_models.Clone.t_Clone t_ReshareNetwork =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

/// Create a new reshare network.
/// `total_participants` is `n_old + n_new` (or fewer if groups overlap).
let impl_ReshareNetwork__new (total_participants: u32) : t_ReshareNetwork =
  let
  (sender: Tokio.Sync.Broadcast.t_Sender Golden_rs.Types.t_ReshareMsg),
  (_: Tokio.Sync.Broadcast.t_Receiver Golden_rs.Types.t_ReshareMsg) =
    Tokio.Sync.Broadcast.channel #Golden_rs.Types.t_ReshareMsg
      (cast (total_participants *! mk_u32 2 <: u32) <: usize)
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
    f_old_members
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
    f_new_members
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
      (Tokio.Sync.Barrier.impl_Barrier__new (cast (total_participants <: u32) <: usize)
        <:
        Tokio.Sync.Barrier.t_Barrier);
    f_session_id = Alloc.Sync.impl_16__new #(t_Array u8 (mk_usize 32)) session_id
  }
  <:
  t_ReshareNetwork

/// Get the session ID for this reshare session.
let impl_ReshareNetwork__session_id (self: t_ReshareNetwork) : t_Array u8 (mk_usize 32) =
  Core_models.Ops.Deref.f_deref #(Alloc.Sync.t_Arc (t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global)
    #FStar.Tactics.Typeclasses.solve
    self.f_session_id

/// Register an old group member with proof of knowledge.
/// Rejects registration if the Schnorr PoK is invalid (prevents rogue-key attacks).
let impl_ReshareNetwork__register_old
      (self: t_ReshareNetwork)
      (id: u32)
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (pok: Golden_rs.Schnorr_pok.t_SchnorrPoK)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Register a new group member with proof of knowledge.
/// Rejects registration if the Schnorr PoK is invalid (prevents rogue-key attacks).
let impl_ReshareNetwork__register_new
      (self: t_ReshareNetwork)
      (id: u32)
      (pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (pok: Golden_rs.Schnorr_pok.t_SchnorrPoK)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Wait for all participants (old + new) to register.
let impl_ReshareNetwork__wait_ready (self: t_ReshareNetwork) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Broadcast a reshare message (called by old nodes).
let impl_ReshareNetwork__broadcast (self: t_ReshareNetwork) (msg: Golden_rs.Types.t_ReshareMsg)
    : Prims.unit =
  let _:Core_models.Result.t_Result usize
    (Tokio.Sync.Broadcast.Error.t_SendError Golden_rs.Types.t_ReshareMsg) =
    Tokio.Sync.Broadcast.impl_3__send #Golden_rs.Types.t_ReshareMsg self.f_sender msg
  in
  ()

/// Get old group member identity keys.
let impl_ReshareNetwork__get_old_members (self: t_ReshareNetwork) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Get new group member identity keys.
let impl_ReshareNetwork__get_new_members (self: t_ReshareNetwork) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""
