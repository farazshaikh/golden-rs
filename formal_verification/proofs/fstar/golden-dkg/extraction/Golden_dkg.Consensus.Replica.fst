module Golden_dkg.Consensus.Replica
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Golden_dkg.Consensus.Types in
  let open Golden_dkg.Threshold.Types in
  let open Rand.Rng in
  let open Rand.Rngs.Thread in
  let open Rand_core in
  let open Std.Hash.Random in
  ()

/// A Simplex consensus replica (one participant's state machine).
/// Paper (Section 2.1): "each process p keeps track of which iteration h
/// it is currently in, and also stores all of the notarized blocks and
/// messages that it has seen thus far."
type t_Replica = {
  f_id:u32;
  f_share:Golden_dkg.Threshold.Types.t_KeyShare;
  f_config:Golden_dkg.Consensus.Types.t_NetworkConfig;
  f_current_view:u64;
  f_voted_in_view:bool;
  f_timer_fired:bool;
  f_finalize_sent:bool;
  f_dummy_sent:bool;
  f_voted_block:Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block;
  f_known_blocks:Std.Collections.Hash.Map.t_HashMap (t_Array u8 (mk_usize 32))
    Golden_dkg.Consensus.Types.t_Block
    Std.Hash.Random.t_RandomState;
  f_notarize_votes:Std.Collections.Hash.Map.t_HashMap (t_Array u8 (mk_usize 32))
    (Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature) Alloc.Alloc.t_Global)
    Std.Hash.Random.t_RandomState;
  f_nullify_votes:Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
    Alloc.Alloc.t_Global;
  f_finalize_votes:Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
    Alloc.Alloc.t_Global;
  f_notarized_in_view:Core_models.Option.t_Option (t_Array u8 (mk_usize 32));
  f_chain_state:Golden_dkg.Consensus.Types.t_ChainState
}

/// Create a new Replica in the genesis state.
/// Paper: "each process starts in iteration h = 1."
let impl_Replica__new
      (id: u32)
      (share: Golden_dkg.Threshold.Types.t_KeyShare)
      (config: Golden_dkg.Consensus.Types.t_NetworkConfig)
    : t_Replica =
  {
    f_id = id;
    f_share = share;
    f_config = config;
    f_current_view = mk_u64 1;
    f_voted_in_view = false;
    f_timer_fired = false;
    f_finalize_sent = false;
    f_dummy_sent = false;
    f_voted_block
    =
    Core_models.Option.Option_None <: Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block;
    f_known_blocks
    =
    Std.Collections.Hash.Map.impl__new #(t_Array u8 (mk_usize 32))
      #Golden_dkg.Consensus.Types.t_Block
      ();
    f_notarize_votes
    =
    Std.Collections.Hash.Map.impl__new #(t_Array u8 (mk_usize 32))
      #(Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature) Alloc.Alloc.t_Global)
      ();
    f_nullify_votes = Alloc.Vec.impl__new #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature) ();
    f_finalize_votes = Alloc.Vec.impl__new #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature) ();
    f_notarized_in_view
    =
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Array u8 (mk_usize 32));
    f_chain_state = Golden_dkg.Consensus.Types.impl_ChainState__genesis ()
  }
  <:
  t_Replica

/// Current view the replica is in.
let impl_Replica__current_view (self: t_Replica) : u64 = self.f_current_view

/// Current chain state (tip hash, VRF seed, counters).
let impl_Replica__chain_state (self: t_Replica) : Golden_dkg.Consensus.Types.t_ChainState =
  self.f_chain_state

/// This replica's node ID.
let impl_Replica__id (self: t_Replica) : u32 = self.f_id

/// Who is the designated leader for the current view.
/// Paper (Section 2.1): "L_h := H*(h) mod n, where H* is a random
/// leader election oracle." We use the VRF seed from the previous
/// notarization as input to SHA-256.
let impl_Replica__leader_for (self: t_Replica) (e_view: u64) : u32 =
  Golden_dkg.Consensus.Vrf.elect_leader (self.f_chain_state.Golden_dkg.Consensus.Types.f_vrf_seed
      <:
      t_Slice u8)
    self.f_config.Golden_dkg.Consensus.Types.f_n

/// Access this replica's threshold key share (for vetKD operations).
let impl_Replica__key_share (self: t_Replica) : Golden_dkg.Threshold.Types.t_KeyShare = self.f_share

/// Access this replica's network config.
let impl_Replica__network_config (self: t_Replica) : Golden_dkg.Consensus.Types.t_NetworkConfig =
  self.f_config

/// Produce an encrypted key share for the given identity.
/// Mirrors DFINITY's per-node behavior in `vetkd_derive_key`:
/// each node computes its partial BLS signature on the identity,
/// encrypts it under the user's transport public key, and returns
/// the encrypted share. The share is publicly verifiable via pairing
/// without revealing the partial signature.
/// This is a **pure function** on the replica's key share -- no
/// consensus state is modified, no messages are queued.
let impl_Replica__vetkd_encrypted_key_share
      (self: t_Replica)
      (identity: t_Slice u8)
      (tpk: Golden_dkg.Threshold.Ibe.t_TransportPublicKey)
    : Golden_dkg.Threshold.Ibe.t_EncryptedKeyShare =
  let rng:Rand.Rngs.Thread.t_ThreadRng = Rand.Rngs.Thread.thread_rng () in
  let (tmp0: Rand.Rngs.Thread.t_ThreadRng), (out: Golden_dkg.Threshold.Ibe.t_EncryptedKeyShare) =
    Golden_dkg.Threshold.Ibe.encrypt_key_share #Rand.Rngs.Thread.t_ThreadRng
      self.f_share
      identity
      tpk
      rng
  in
  let rng:Rand.Rngs.Thread.t_ThreadRng = tmp0 in
  out

/// Accumulate a notarization vote `<vote, h, b_h>` from another node.
/// Paper Step 4: "On seeing a notarized blockchain of height h, enter
/// iteration h+1." Accepts notarization for ANY block at the current
/// height, even one this replica didn't vote for.
let impl_Replica__handle_vote
      (self: t_Replica)
      (view: u64)
      (bh: t_Array u8 (mk_usize 32))
      (signer: u32)
      (partial: Golden_dkg.Threshold.Types.t_PartialSignature)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    if Core_models.Option.impl__is_some #(t_Array u8 (mk_usize 32)) self.f_notarized_in_view
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
        "{\n let votes: &mut alloc::vec::t_Vec<\n tuple2<int, golden_dkg::threshold::types::t_PartialSignature>,\n alloc::alloc::t_Global,\n > = {\n std::collections::hash::map::impl_73__or_default::<\n lifetime!(so..."

/// Check if finalize votes reached >= 2n/3.
/// Paper Step 5: "Whenever p sees a finalized blockchain b_0,...,b_{h'},
/// output the contents LOG <- linearize(b_0,...,b_{h'})."
/// A block is finalized when it is notarized AND has >= 2n/3 finalize votes.
let impl_Replica__try_finalize (self: t_Replica) (view: u64)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  let threshold:usize = cast (self.f_config.Golden_dkg.Consensus.Types.f_t <: u32) <: usize in
  if
    (Alloc.Vec.impl_1__len #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
        #Alloc.Alloc.t_Global
        self.f_finalize_votes
      <:
      usize) <.
    threshold
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let self:t_Replica =
      {
        self with
        f_chain_state
        =
        {
          self.f_chain_state with
          Golden_dkg.Consensus.Types.f_finalized_count
          =
          self.f_chain_state.Golden_dkg.Consensus.Types.f_finalized_count +! mk_u64 1
        }
        <:
        Golden_dkg.Consensus.Types.t_ChainState
      }
      <:
      t_Replica
    in
    let bh:t_Array u8 (mk_usize 32) =
      Core_models.Option.impl__unwrap_or #(t_Array u8 (mk_usize 32))
        self.f_notarized_in_view
        (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) <: t_Array u8 (mk_usize 32))
    in
    let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
      Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
      (Golden_dkg.Consensus.Types.StateTransition_Finalized
        ({ Golden_dkg.Consensus.Types.f_view = view; Golden_dkg.Consensus.Types.f_block_hash = bh })
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
    in
    self, hax_temp_output
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Accumulate a finalize vote `<finalize, h>` from another node.
/// Paper Step 5: When >= 2n/3 finalize votes are collected for height h
/// where a block is already notarized, the block is finalized.
let impl_Replica__handle_finalize_vote
      (self: t_Replica)
      (view: u64)
      (signer: u32)
      (partial: Golden_dkg.Threshold.Types.t_PartialSignature)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if
    view <>. self.f_current_view &&
    view <>. (Core_models.Num.impl_u64__saturating_sub self.f_current_view (mk_u64 1) <: u64)
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let
    (_: Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)),
    (out: bool) =
      Core_models.Iter.Traits.Iterator.f_any #(Core_models.Slice.Iter.t_Iter
          (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        #FStar.Tactics.Typeclasses.solve
        #((u32 & Golden_dkg.Threshold.Types.t_PartialSignature) -> bool)
        (Core_models.Slice.impl__iter #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
            (Alloc.Vec.impl_1__as_slice self.f_finalize_votes
              <:
              t_Slice (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
          <:
          Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        (fun temp_0_ ->
            let (id: u32), (_: Golden_dkg.Threshold.Types.t_PartialSignature) = temp_0_ in
            id =. signer <: bool)
    in
    if out
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let self:t_Replica =
        {
          self with
          f_finalize_votes
          =
          Alloc.Vec.impl_1__push #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
            #Alloc.Alloc.t_Global
            self.f_finalize_votes
            (signer, partial <: (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        }
        <:
        t_Replica
      in
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__try_finalize self view
      in
      let self:t_Replica = tmp0 in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        out
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Advance to the next view, resetting all per-view state.
/// Paper: "enter iteration h+1" -- each process advances independently.
let impl_Replica__advance_view (self: t_Replica) : t_Replica =
  let self:t_Replica =
    { self with f_current_view = self.f_current_view +! mk_u64 1 } <: t_Replica
  in
  let self:t_Replica = { self with f_voted_in_view = false } <: t_Replica in
  let self:t_Replica = { self with f_timer_fired = false } <: t_Replica in
  let self:t_Replica = { self with f_finalize_sent = false } <: t_Replica in
  let self:t_Replica = { self with f_dummy_sent = false } <: t_Replica in
  let self:t_Replica =
    {
      self with
      f_voted_block
      =
      Core_models.Option.Option_None
      <:
      Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block
    }
    <:
    t_Replica
  in
  let self:t_Replica =
    {
      self with
      f_known_blocks
      =
      Std.Collections.Hash.Map.impl_1__clear #(t_Array u8 (mk_usize 32))
        #Golden_dkg.Consensus.Types.t_Block
        #Std.Hash.Random.t_RandomState
        self.f_known_blocks
    }
    <:
    t_Replica
  in
  let self:t_Replica =
    {
      self with
      f_notarize_votes
      =
      Std.Collections.Hash.Map.impl_1__clear #(t_Array u8 (mk_usize 32))
        #(Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature) Alloc.Alloc.t_Global
        )
        #Std.Hash.Random.t_RandomState
        self.f_notarize_votes
    }
    <:
    t_Replica
  in
  let self:t_Replica =
    {
      self with
      f_nullify_votes
      =
      Alloc.Vec.impl_1__clear #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
        #Alloc.Alloc.t_Global
        self.f_nullify_votes
    }
    <:
    t_Replica
  in
  let self:t_Replica =
    {
      self with
      f_finalize_votes
      =
      Alloc.Vec.impl_1__clear #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
        #Alloc.Alloc.t_Global
        self.f_finalize_votes
    }
    <:
    t_Replica
  in
  let self:t_Replica =
    {
      self with
      f_notarized_in_view
      =
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Array u8 (mk_usize 32))
    }
    <:
    t_Replica
  in
  self

/// Check if nullify (dummy) votes reached >= 2n/3.
/// Paper: "If T_h fires, vote <vote, h, ⊥_h>." When >= 2n/3 dummy
/// votes are collected, the dummy block is notarized and all nodes
/// advance to iteration h+1. The tip_hash does NOT change (dummy
/// blocks don't extend the chain content).
let impl_Replica__try_nullify (self: t_Replica) (view: u64)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if Core_models.Option.impl__is_some #(t_Array u8 (mk_usize 32)) self.f_notarized_in_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let threshold:usize = cast (self.f_config.Golden_dkg.Consensus.Types.f_t <: u32) <: usize in
    if
      (Alloc.Vec.impl_1__len #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
          #Alloc.Alloc.t_Global
          self.f_nullify_votes
        <:
        usize) <.
      threshold
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let self:t_Replica =
        {
          self with
          f_notarized_in_view
          =
          Core_models.Option.Option_Some (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32))
          <:
          Core_models.Option.t_Option (t_Array u8 (mk_usize 32))
        }
        <:
        t_Replica
      in
      let
      (partials: Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
        Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global =
        Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
              (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              ((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature))
          #FStar.Tactics.Typeclasses.solve
          #(Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global)
          (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
                (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              #FStar.Tactics.Typeclasses.solve
              #Golden_dkg.Threshold.Types.t_PartialSignature
              #((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature)
              (Core_models.Slice.impl__iter #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  (Alloc.Vec.impl_1__as_slice self.f_nullify_votes
                    <:
                    t_Slice (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
                <:
                Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              (fun temp_0_ ->
                  let (_: u32), (p: Golden_dkg.Threshold.Types.t_PartialSignature) = temp_0_ in
                  Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_PartialSignature
                    #FStar.Tactics.Typeclasses.solve
                    p
                  <:
                  Golden_dkg.Threshold.Types.t_PartialSignature)
            <:
            Core_models.Iter.Adapters.Map.t_Map
              (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              ((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature))
      in
      let combined:Golden_dkg.Threshold.Types.t_ThresholdSignature =
        Golden_dkg.Threshold.Signing.combine_dynamic (Alloc.Vec.impl_1__as_slice partials
            <:
            t_Slice Golden_dkg.Threshold.Types.t_PartialSignature)
          threshold
      in
      let sig_bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Golden_dkg.Threshold.Beacon.g2_to_bytes combined.Golden_dkg.Threshold.Types.f_signature
      in
      let vrf_seed:t_Array u8 (mk_usize 32) =
        Golden_dkg.Threshold.Beacon.derive_randomness (Alloc.Vec.impl_1__as_slice sig_bytes
            <:
            t_Slice u8)
      in
      let self:t_Replica =
        {
          self with
          f_chain_state
          =
          { self.f_chain_state with Golden_dkg.Consensus.Types.f_vrf_seed = vrf_seed }
          <:
          Golden_dkg.Consensus.Types.t_ChainState
        }
        <:
        t_Replica
      in
      let self:t_Replica =
        {
          self with
          f_chain_state
          =
          {
            self.f_chain_state with
            Golden_dkg.Consensus.Types.f_nullified_count
            =
            self.f_chain_state.Golden_dkg.Consensus.Types.f_nullified_count +! mk_u64 1
          }
          <:
          Golden_dkg.Consensus.Types.t_ChainState
        }
        <:
        t_Replica
      in
      let self:t_Replica = impl_Replica__advance_view self in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        (Golden_dkg.Consensus.Types.StateTransition_Nullified
          ({ Golden_dkg.Consensus.Types.f_view = view })
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Accumulate a nullification vote `<vote, h, ⊥_h>` from another node.
let impl_Replica__handle_nullify_vote
      (self: t_Replica)
      (view: u64)
      (signer: u32)
      (partial: Golden_dkg.Threshold.Types.t_PartialSignature)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let
    (_: Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)),
    (out: bool) =
      Core_models.Iter.Traits.Iterator.f_any #(Core_models.Slice.Iter.t_Iter
          (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        #FStar.Tactics.Typeclasses.solve
        #((u32 & Golden_dkg.Threshold.Types.t_PartialSignature) -> bool)
        (Core_models.Slice.impl__iter #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
            (Alloc.Vec.impl_1__as_slice self.f_nullify_votes
              <:
              t_Slice (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
          <:
          Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        (fun temp_0_ ->
            let (id: u32), (_: Golden_dkg.Threshold.Types.t_PartialSignature) = temp_0_ in
            id =. signer <: bool)
    in
    if out
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let self:t_Replica =
        {
          self with
          f_nullify_votes
          =
          Alloc.Vec.impl_1__push #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
            #Alloc.Alloc.t_Global
            self.f_nullify_votes
            (signer, partial <: (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        }
        <:
        t_Replica
      in
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__try_nullify self view
      in
      let self:t_Replica = tmp0 in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        out
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Sign `<vote, h, b_h>` -- a notarization vote bound to a specific block.
let impl_Replica__sign_vote (self: t_Replica) (view: u64) (bh: t_Array u8 (mk_usize 32))
    : Golden_dkg.Threshold.Types.t_PartialSignature =
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec #u8 (Core_models.Num.impl_u64__to_be_bytes view <: t_Slice u8)
  in
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8 #Alloc.Alloc.t_Global msg (bh <: t_Slice u8)
  in
  let digest:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Golden_dkg.Threshold.Beacon.digest_message view
      (Core_models.Option.Option_Some (Alloc.Vec.impl_1__as_slice msg <: t_Slice u8)
        <:
        Core_models.Option.t_Option (t_Slice u8))
  in
  let msg_hash:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Golden_dkg.Threshold.Beacon.hash_to_g2 (Alloc.Vec.impl_1__as_slice digest <: t_Slice u8)
  in
  Golden_dkg.Threshold.Signing.partial_sign msg_hash self.f_share

/// Handle a request to propose a block (leader only).
/// The replica checks it IS the designated leader, builds a block from
/// its own `chain_state.tip_hash`, votes for it, and returns both
/// [`Outgoing::Proposal`] and [`Outgoing::Vote`].
let impl_Replica__handle_propose_request
      (self: t_Replica)
      (view: u64)
      (payload: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let leader:u32 = impl_Replica__leader_for self view in
    if leader <>. self.f_id
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let block:Golden_dkg.Consensus.Types.t_Block =
        {
          Golden_dkg.Consensus.Types.f_view = view;
          Golden_dkg.Consensus.Types.f_parent_hash
          =
          self.f_chain_state.Golden_dkg.Consensus.Types.f_tip_hash;
          Golden_dkg.Consensus.Types.f_payload = payload;
          Golden_dkg.Consensus.Types.f_proposer = self.f_id
        }
        <:
        Golden_dkg.Consensus.Types.t_Block
      in
      let bh:t_Array u8 (mk_usize 32) = Golden_dkg.Consensus.Types.block_hash block in
      let self:t_Replica = { self with f_voted_in_view = true } <: t_Replica in
      let self:t_Replica =
        {
          self with
          f_voted_block
          =
          Core_models.Option.Option_Some
          (Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
              #FStar.Tactics.Typeclasses.solve
              block)
          <:
          Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block
        }
        <:
        t_Replica
      in
      let
      (tmp0:
        Std.Collections.Hash.Map.t_HashMap (t_Array u8 (mk_usize 32))
          Golden_dkg.Consensus.Types.t_Block
          Std.Hash.Random.t_RandomState),
      (out: Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block) =
        Std.Collections.Hash.Map.impl_2__insert #(t_Array u8 (mk_usize 32))
          #Golden_dkg.Consensus.Types.t_Block
          #Std.Hash.Random.t_RandomState
          self.f_known_blocks
          bh
          (Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
              #FStar.Tactics.Typeclasses.solve
              block
            <:
            Golden_dkg.Consensus.Types.t_Block)
      in
      let self:t_Replica = { self with f_known_blocks = tmp0 } <: t_Replica in
      let _:Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block = out in
      let sig:Golden_dkg.Threshold.Types.t_PartialSignature =
        impl_Replica__sign_vote self view bh
      in
      let _:Prims.unit =
        Rust_primitives.Hax.failure "Explicit rejection by a phase in the Hax engine:\na node of kind [Arbitrary_lhs] have been found in the AST\n\nNote: the error was labeled with context `reject_ArbitraryLhs`.\n"
          "(rust_primitives::hax::failure(\n \"At this position, Hax was expecting an expression of the shape `&mut _`.\nHax forbids `f(x)` (where `f` expects a mutable reference as input) when `x` is not a place ..."

      in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        (Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Slice.impl__into_vec #Golden_dkg.Consensus.Types.t_Outgoing
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  Golden_dkg.Consensus.Types.Outgoing_Proposal
                  ({ Golden_dkg.Consensus.Types.f_block = block })
                  <:
                  Golden_dkg.Consensus.Types.t_Outgoing;
                  Golden_dkg.Consensus.Types.Outgoing_Vote
                  ({
                      Golden_dkg.Consensus.Types.f_view = view;
                      Golden_dkg.Consensus.Types.f_block_hash = bh;
                      Golden_dkg.Consensus.Types.f_partial = sig
                    })
                  <:
                  Golden_dkg.Consensus.Types.t_Outgoing
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            <:
            t_Slice Golden_dkg.Consensus.Types.t_Outgoing)
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Sign `<vote, h, ⊥_h>` -- a nullification (dummy) vote.
let impl_Replica__sign_dummy (self: t_Replica) (view: u64)
    : Golden_dkg.Threshold.Types.t_PartialSignature =
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Golden_dkg.Consensus.Vrf.vrf_message view in
  let digest:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Golden_dkg.Threshold.Beacon.digest_message view
      (Core_models.Option.Option_Some (Alloc.Vec.impl_1__as_slice msg <: t_Slice u8)
        <:
        Core_models.Option.t_Option (t_Slice u8))
  in
  let msg_hash:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Golden_dkg.Threshold.Beacon.hash_to_g2 (Alloc.Vec.impl_1__as_slice digest <: t_Slice u8)
  in
  Golden_dkg.Threshold.Signing.partial_sign msg_hash self.f_share

/// Handle timer firing: produce a dummy (nullification) vote.
/// **Lemma 3.3 enforcement**: if `finalize_sent` or `dummy_sent` is
/// already true, this is a no-op. An honest node NEVER sends both
/// `<finalize, h>` and `<vote, h, ⊥_h>`.
let impl_Replica__handle_timeout (self: t_Replica) (view: u64)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    if self.f_finalize_sent || self.f_dummy_sent
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let self:t_Replica = { self with f_timer_fired = true } <: t_Replica in
      let self:t_Replica = { self with f_dummy_sent = true } <: t_Replica in
      let sig:Golden_dkg.Threshold.Types.t_PartialSignature = impl_Replica__sign_dummy self view in
      let self:t_Replica =
        {
          self with
          f_nullify_votes
          =
          Alloc.Vec.impl_1__push #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
            #Alloc.Alloc.t_Global
            self.f_nullify_votes
            (self.f_id,
              (Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_PartialSignature
                  #FStar.Tactics.Typeclasses.solve
                  sig
                <:
                Golden_dkg.Threshold.Types.t_PartialSignature)
              <:
              (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
        }
        <:
        t_Replica
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Alloc.Slice.impl__into_vec #Golden_dkg.Consensus.Types.t_Outgoing
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  Golden_dkg.Consensus.Types.Outgoing_NullifyVote
                  ({
                      Golden_dkg.Consensus.Types.f_view = view;
                      Golden_dkg.Consensus.Types.f_partial = sig
                    })
                  <:
                  Golden_dkg.Consensus.Types.t_Outgoing
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice Golden_dkg.Consensus.Types.t_Outgoing)
      in
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__try_nullify self view
      in
      let self:t_Replica = tmp0 in
      let
      (transition: Golden_dkg.Consensus.Types.t_StateTransition),
      (extra: Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        out
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Core_models.Iter.Traits.Collect.f_extend #(Alloc.Vec.t_Vec
              Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
          #Golden_dkg.Consensus.Types.t_Outgoing
          #FStar.Tactics.Typeclasses.solve
          #(Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
          outgoing
          extra
      in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        transition, outgoing
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Sign `<finalize, h>` -- a finalization vote.
let impl_Replica__sign_finalize (self: t_Replica) (view: u64)
    : Golden_dkg.Threshold.Types.t_PartialSignature =
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec #u8
      ((let list =
            [
              mk_u8 102;
              mk_u8 105;
              mk_u8 110;
              mk_u8 97;
              mk_u8 108;
              mk_u8 105;
              mk_u8 122;
              mk_u8 101;
              mk_u8 45
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
          Rust_primitives.Hax.array_of_list 9 list)
        <:
        t_Slice u8)
  in
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      msg
      (Core_models.Num.impl_u64__to_be_bytes view <: t_Slice u8)
  in
  let digest:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Golden_dkg.Threshold.Beacon.digest_message view
      (Core_models.Option.Option_Some (Alloc.Vec.impl_1__as_slice msg <: t_Slice u8)
        <:
        Core_models.Option.t_Option (t_Slice u8))
  in
  let msg_hash:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Golden_dkg.Threshold.Beacon.hash_to_g2 (Alloc.Vec.impl_1__as_slice digest <: t_Slice u8)
  in
  Golden_dkg.Threshold.Signing.partial_sign msg_hash self.f_share

/// Handle a relayed notarization from another node.
/// Accepts the notarization even if this replica didn't vote for the
/// block. This is how honest nodes catch up after missing a proposal.
let impl_Replica__handle_notarization
      (self: t_Replica)
      (view: u64)
      (block: Golden_dkg.Consensus.Types.t_Block)
      (e_certificate: Golden_dkg.Consensus.Types.t_Certificate)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    if Core_models.Option.impl__is_some #(t_Array u8 (mk_usize 32)) self.f_notarized_in_view
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let bh:t_Array u8 (mk_usize 32) = Golden_dkg.Consensus.Types.block_hash block in
      let self:t_Replica =
        {
          self with
          f_notarized_in_view
          =
          Core_models.Option.Option_Some bh
          <:
          Core_models.Option.t_Option (t_Array u8 (mk_usize 32))
        }
        <:
        t_Replica
      in
      let self:t_Replica =
        {
          self with
          f_chain_state
          =
          { self.f_chain_state with Golden_dkg.Consensus.Types.f_tip_hash = bh }
          <:
          Golden_dkg.Consensus.Types.t_ChainState
        }
        <:
        t_Replica
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      in
      let
      (outgoing: Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global),
      (self: t_Replica) =
        if ~.self.f_timer_fired && ~.self.f_finalize_sent
        then
          let self:t_Replica = { self with f_finalize_sent = true } <: t_Replica in
          let sig:Golden_dkg.Threshold.Types.t_PartialSignature =
            impl_Replica__sign_finalize self view
          in
          let self:t_Replica =
            {
              self with
              f_finalize_votes
              =
              Alloc.Vec.impl_1__push #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                #Alloc.Alloc.t_Global
                self.f_finalize_votes
                (self.f_id,
                  (Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_PartialSignature
                      #FStar.Tactics.Typeclasses.solve
                      sig
                    <:
                    Golden_dkg.Threshold.Types.t_PartialSignature)
                  <:
                  (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
            }
            <:
            t_Replica
          in
          let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #Golden_dkg.Consensus.Types.t_Outgoing
              #Alloc.Alloc.t_Global
              outgoing
              (Golden_dkg.Consensus.Types.Outgoing_FinalizeVote
                ({
                    Golden_dkg.Consensus.Types.f_view = view;
                    Golden_dkg.Consensus.Types.f_partial = sig
                  })
                <:
                Golden_dkg.Consensus.Types.t_Outgoing)
          in
          outgoing, self
          <:
          (Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global & t_Replica)
        else
          outgoing, self
          <:
          (Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global & t_Replica)
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__push #Golden_dkg.Consensus.Types.t_Outgoing
          #Alloc.Alloc.t_Global
          outgoing
          (Golden_dkg.Consensus.Types.Outgoing_RelayNotarization
            ({
                Golden_dkg.Consensus.Types.f_view = view;
                Golden_dkg.Consensus.Types.f_block
                =
                Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
                  #FStar.Tactics.Typeclasses.solve
                  block
                <:
                Golden_dkg.Consensus.Types.t_Block;
                Golden_dkg.Consensus.Types.f_certificate = e_certificate
              })
            <:
            Golden_dkg.Consensus.Types.t_Outgoing)
      in
      let self:t_Replica = impl_Replica__advance_view self in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        (Golden_dkg.Consensus.Types.StateTransition_Notarized
          ({
              Golden_dkg.Consensus.Types.f_view = view;
              Golden_dkg.Consensus.Types.f_block_hash = bh
            })
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        outgoing
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Check if notarization votes for a block reached >= 2n/3.
/// Paper: "A notarization for a block b is a set of signed messages
/// `<vote, h, b>` from >= 2n/3 unique processes."
/// On reaching threshold:
/// 1. Mark block as notarized
/// 2. Update `chain_state.tip_hash`
/// 3. If timer has NOT fired, send `<finalize, h>` (Paper Step 4, Lemma 3.3)
/// 4. Derive VRF seed from the combined threshold signature
/// 5. Relay the notarized blockchain
/// 6. Advance to next view
let impl_Replica__try_notarize
      (self: t_Replica)
      (view: u64)
      (bh: t_Array u8 (mk_usize 32))
      (block: Golden_dkg.Consensus.Types.t_Block)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  if Core_models.Option.impl__is_some #(t_Array u8 (mk_usize 32)) self.f_notarized_in_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Pending
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let threshold:usize = cast (self.f_config.Golden_dkg.Consensus.Types.f_t <: u32) <: usize in
    let count:usize =
      Core_models.Option.impl__map_or #(Alloc.Vec.t_Vec
            (u32 & Golden_dkg.Threshold.Types.t_PartialSignature) Alloc.Alloc.t_Global)
        #usize
        #(Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature) Alloc.Alloc.t_Global
            -> usize)
        (Std.Collections.Hash.Map.impl_2__get #(t_Array u8 (mk_usize 32))
            #(Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                Alloc.Alloc.t_Global)
            #Std.Hash.Random.t_RandomState
            #(t_Array u8 (mk_usize 32))
            self.f_notarize_votes
            bh
          <:
          Core_models.Option.t_Option
          (Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
              Alloc.Alloc.t_Global))
        (mk_usize 0)
        (fun v ->
            let v:Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
              Alloc.Alloc.t_Global =
              v
            in
            Alloc.Vec.impl_1__len #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
              #Alloc.Alloc.t_Global
              v
            <:
            usize)
    in
    if count <. threshold
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Pending
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      let self:t_Replica =
        {
          self with
          f_notarized_in_view
          =
          Core_models.Option.Option_Some bh
          <:
          Core_models.Option.t_Option (t_Array u8 (mk_usize 32))
        }
        <:
        t_Replica
      in
      let self:t_Replica =
        {
          self with
          f_chain_state
          =
          { self.f_chain_state with Golden_dkg.Consensus.Types.f_tip_hash = bh }
          <:
          Golden_dkg.Consensus.Types.t_ChainState
        }
        <:
        t_Replica
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      in
      let
      (outgoing: Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global),
      (self: t_Replica) =
        if ~.self.f_timer_fired && ~.self.f_finalize_sent
        then
          let self:t_Replica = { self with f_finalize_sent = true } <: t_Replica in
          let sig:Golden_dkg.Threshold.Types.t_PartialSignature =
            impl_Replica__sign_finalize self view
          in
          let self:t_Replica =
            {
              self with
              f_finalize_votes
              =
              Alloc.Vec.impl_1__push #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                #Alloc.Alloc.t_Global
                self.f_finalize_votes
                (self.f_id,
                  (Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_PartialSignature
                      #FStar.Tactics.Typeclasses.solve
                      sig
                    <:
                    Golden_dkg.Threshold.Types.t_PartialSignature)
                  <:
                  (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
            }
            <:
            t_Replica
          in
          let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #Golden_dkg.Consensus.Types.t_Outgoing
              #Alloc.Alloc.t_Global
              outgoing
              (Golden_dkg.Consensus.Types.Outgoing_FinalizeVote
                ({
                    Golden_dkg.Consensus.Types.f_view = view;
                    Golden_dkg.Consensus.Types.f_partial = sig
                  })
                <:
                Golden_dkg.Consensus.Types.t_Outgoing)
          in
          outgoing, self
          <:
          (Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global & t_Replica)
        else
          outgoing, self
          <:
          (Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global & t_Replica)
      in
      let
      (partials: Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
        Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global =
        Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
              (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              ((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature))
          #FStar.Tactics.Typeclasses.solve
          #(Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_PartialSignature Alloc.Alloc.t_Global)
          (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
                (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              #FStar.Tactics.Typeclasses.solve
              #Golden_dkg.Threshold.Types.t_PartialSignature
              #((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature)
              (Core_models.Slice.impl__iter #(u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  (Alloc.Vec.impl_1__as_slice (Core_models.Option.impl__unwrap #(Alloc.Vec.t_Vec
                              (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                              Alloc.Alloc.t_Global)
                          (Std.Collections.Hash.Map.impl_2__get #(t_Array u8 (mk_usize 32))
                              #(Alloc.Vec.t_Vec
                                  (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                                  Alloc.Alloc.t_Global)
                              #Std.Hash.Random.t_RandomState
                              #(t_Array u8 (mk_usize 32))
                              self.f_notarize_votes
                              bh
                            <:
                            Core_models.Option.t_Option
                            (Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                                Alloc.Alloc.t_Global))
                        <:
                        Alloc.Vec.t_Vec (u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                          Alloc.Alloc.t_Global)
                    <:
                    t_Slice (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
                <:
                Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              (fun temp_0_ ->
                  let (_: u32), (p: Golden_dkg.Threshold.Types.t_PartialSignature) = temp_0_ in
                  Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_PartialSignature
                    #FStar.Tactics.Typeclasses.solve
                    p
                  <:
                  Golden_dkg.Threshold.Types.t_PartialSignature)
            <:
            Core_models.Iter.Adapters.Map.t_Map
              (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Threshold.Types.t_PartialSignature))
              ((u32 & Golden_dkg.Threshold.Types.t_PartialSignature)
                  -> Golden_dkg.Threshold.Types.t_PartialSignature))
      in
      let combined:Golden_dkg.Threshold.Types.t_ThresholdSignature =
        Golden_dkg.Threshold.Signing.combine_dynamic (Alloc.Vec.impl_1__as_slice partials
            <:
            t_Slice Golden_dkg.Threshold.Types.t_PartialSignature)
          threshold
      in
      let cert:Golden_dkg.Consensus.Types.t_Certificate =
        {
          Golden_dkg.Consensus.Types.f_view = view;
          Golden_dkg.Consensus.Types.f_kind
          =
          Golden_dkg.Consensus.Types.CertKind_Notarization bh
          <:
          Golden_dkg.Consensus.Types.t_CertKind;
          Golden_dkg.Consensus.Types.f_signature = combined.Golden_dkg.Threshold.Types.f_signature
        }
        <:
        Golden_dkg.Consensus.Types.t_Certificate
      in
      let sig_bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Golden_dkg.Threshold.Beacon.g2_to_bytes combined.Golden_dkg.Threshold.Types.f_signature
      in
      let vrf_seed:t_Array u8 (mk_usize 32) =
        Golden_dkg.Threshold.Beacon.derive_randomness (Alloc.Vec.impl_1__as_slice sig_bytes
            <:
            t_Slice u8)
      in
      let self:t_Replica =
        {
          self with
          f_chain_state
          =
          { self.f_chain_state with Golden_dkg.Consensus.Types.f_vrf_seed = vrf_seed }
          <:
          Golden_dkg.Consensus.Types.t_ChainState
        }
        <:
        t_Replica
      in
      let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__push #Golden_dkg.Consensus.Types.t_Outgoing
          #Alloc.Alloc.t_Global
          outgoing
          (Golden_dkg.Consensus.Types.Outgoing_RelayNotarization
            ({
                Golden_dkg.Consensus.Types.f_view = view;
                Golden_dkg.Consensus.Types.f_block
                =
                Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
                  #FStar.Tactics.Typeclasses.solve
                  block
                <:
                Golden_dkg.Consensus.Types.t_Block;
                Golden_dkg.Consensus.Types.f_certificate = cert
              })
            <:
            Golden_dkg.Consensus.Types.t_Outgoing)
      in
      let self:t_Replica = impl_Replica__advance_view self in
      let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
        (Golden_dkg.Consensus.Types.StateTransition_Notarized
          ({
              Golden_dkg.Consensus.Types.f_view = view;
              Golden_dkg.Consensus.Types.f_block_hash = bh
            })
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        outgoing
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
      in
      self, hax_temp_output
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Handle an incoming proposal from the leader.
/// Validates: correct view, correct leader (L_h), not already voted,
/// and valid parent chain (parent_hash matches tip). If all pass,
/// produces [`Outgoing::Vote`].
/// **Lemma 3.2 enforcement**: `voted_in_view` prevents double-voting.
let impl_Replica__handle_proposal (self: t_Replica) (block: Golden_dkg.Consensus.Types.t_Block)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  let view:u64 = block.Golden_dkg.Consensus.Types.f_view in
  if view <>. self.f_current_view
  then
    self,
    ((Golden_dkg.Consensus.Types.StateTransition_Rejected
        ({
            Golden_dkg.Consensus.Types.f_view = view;
            Golden_dkg.Consensus.Types.f_reason
            =
            Golden_dkg.Consensus.Types.RejectReason_WrongView
            <:
            Golden_dkg.Consensus.Types.t_RejectReason
          })
        <:
        Golden_dkg.Consensus.Types.t_StateTransition),
      Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
      <:
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    <:
    (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  else
    let
    (tmp0:
      Std.Collections.Hash.Map.t_HashMap (t_Array u8 (mk_usize 32))
        Golden_dkg.Consensus.Types.t_Block
        Std.Hash.Random.t_RandomState),
    (out: Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block) =
      Std.Collections.Hash.Map.impl_2__insert #(t_Array u8 (mk_usize 32))
        #Golden_dkg.Consensus.Types.t_Block
        #Std.Hash.Random.t_RandomState
        self.f_known_blocks
        (Golden_dkg.Consensus.Types.block_hash block <: t_Array u8 (mk_usize 32))
        (Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
            #FStar.Tactics.Typeclasses.solve
            block
          <:
          Golden_dkg.Consensus.Types.t_Block)
    in
    let self:t_Replica = { self with f_known_blocks = tmp0 } <: t_Replica in
    let _:Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block = out in
    let leader:u32 = impl_Replica__leader_for self view in
    if block.Golden_dkg.Consensus.Types.f_proposer <>. leader
    then
      self,
      ((Golden_dkg.Consensus.Types.StateTransition_Rejected
          ({
              Golden_dkg.Consensus.Types.f_view = view;
              Golden_dkg.Consensus.Types.f_reason
              =
              Golden_dkg.Consensus.Types.RejectReason_WrongLeader
              <:
              Golden_dkg.Consensus.Types.t_RejectReason
            })
          <:
          Golden_dkg.Consensus.Types.t_StateTransition),
        Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
        <:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    else
      if self.f_voted_in_view
      then
        self,
        ((Golden_dkg.Consensus.Types.StateTransition_Rejected
            ({
                Golden_dkg.Consensus.Types.f_view = view;
                Golden_dkg.Consensus.Types.f_reason
                =
                Golden_dkg.Consensus.Types.RejectReason_AlreadyVoted
                <:
                Golden_dkg.Consensus.Types.t_RejectReason
              })
            <:
            Golden_dkg.Consensus.Types.t_StateTransition),
          Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
          <:
          (Golden_dkg.Consensus.Types.t_StateTransition &
            Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
        <:
        (t_Replica &
          (Golden_dkg.Consensus.Types.t_StateTransition &
            Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
      else
        if
          block.Golden_dkg.Consensus.Types.f_parent_hash <>.
          self.f_chain_state.Golden_dkg.Consensus.Types.f_tip_hash
        then
          self,
          ((Golden_dkg.Consensus.Types.StateTransition_Rejected
              ({
                  Golden_dkg.Consensus.Types.f_view = view;
                  Golden_dkg.Consensus.Types.f_reason
                  =
                  Golden_dkg.Consensus.Types.RejectReason_BadParentHash
                  <:
                  Golden_dkg.Consensus.Types.t_RejectReason
                })
              <:
              Golden_dkg.Consensus.Types.t_StateTransition),
            Alloc.Vec.impl__new #Golden_dkg.Consensus.Types.t_Outgoing ()
            <:
            (Golden_dkg.Consensus.Types.t_StateTransition &
              Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
          <:
          (t_Replica &
            (Golden_dkg.Consensus.Types.t_StateTransition &
              Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
        else
          let self:t_Replica = { self with f_voted_in_view = true } <: t_Replica in
          let self:t_Replica =
            {
              self with
              f_voted_block
              =
              Core_models.Option.Option_Some
              (Core_models.Clone.f_clone #Golden_dkg.Consensus.Types.t_Block
                  #FStar.Tactics.Typeclasses.solve
                  block)
              <:
              Core_models.Option.t_Option Golden_dkg.Consensus.Types.t_Block
            }
            <:
            t_Replica
          in
          let bh:t_Array u8 (mk_usize 32) = Golden_dkg.Consensus.Types.block_hash block in
          let sig:Golden_dkg.Threshold.Types.t_PartialSignature =
            impl_Replica__sign_vote self view bh
          in
          let _:Prims.unit =
            Rust_primitives.Hax.failure "Explicit rejection by a phase in the Hax engine:\na node of kind [Arbitrary_lhs] have been found in the AST\n\nNote: the error was labeled with context `reject_ArbitraryLhs`.\n"
              "(rust_primitives::hax::failure(\n \"At this position, Hax was expecting an expression of the shape `&mut _`.\nHax forbids `f(x)` (where `f` expects a mutable reference as input) when `x` is not a place ..."

          in
          let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
            Alloc.Slice.impl__into_vec #Golden_dkg.Consensus.Types.t_Outgoing
              #Alloc.Alloc.t_Global
              ((let list =
                    [
                      Golden_dkg.Consensus.Types.Outgoing_Vote
                      ({
                          Golden_dkg.Consensus.Types.f_view = view;
                          Golden_dkg.Consensus.Types.f_block_hash = bh;
                          Golden_dkg.Consensus.Types.f_partial = sig
                        })
                      <:
                      Golden_dkg.Consensus.Types.t_Outgoing
                    ]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
                <:
                t_Slice Golden_dkg.Consensus.Types.t_Outgoing)
          in
          let
          (tmp0: t_Replica),
          (out:
            (Golden_dkg.Consensus.Types.t_StateTransition &
              Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
            impl_Replica__try_notarize self view bh block
          in
          let self:t_Replica = tmp0 in
          let
          (transition: Golden_dkg.Consensus.Types.t_StateTransition),
          (extra: Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
            out
          in
          let outgoing:Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global =
            Core_models.Iter.Traits.Collect.f_extend #(Alloc.Vec.t_Vec
                  Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
              #Golden_dkg.Consensus.Types.t_Outgoing
              #FStar.Tactics.Typeclasses.solve
              #(Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
              outgoing
              extra
          in
          let hax_temp_output:(Golden_dkg.Consensus.Types.t_StateTransition &
            Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global) =
            transition, outgoing
            <:
            (Golden_dkg.Consensus.Types.t_StateTransition &
              Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)
          in
          self, hax_temp_output
          <:
          (t_Replica &
            (Golden_dkg.Consensus.Types.t_StateTransition &
              Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))

/// Process one message. Returns the state transition and any outgoing
/// messages the replica wants to broadcast.
/// This is the ONLY entry point for the state machine.
let impl_Replica__apply_message (self: t_Replica) (msg: Golden_dkg.Consensus.Types.t_Message)
    : (t_Replica &
      (Golden_dkg.Consensus.Types.t_StateTransition &
        Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
  let
  (self: t_Replica),
  (hax_temp_output:
    (Golden_dkg.Consensus.Types.t_StateTransition &
      Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
    match msg <: Golden_dkg.Consensus.Types.t_Message with
    | Golden_dkg.Consensus.Types.Message_Proposal { Golden_dkg.Consensus.Types.f_block = block } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_proposal self block
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_Vote
      { Golden_dkg.Consensus.Types.f_view = view ;
        Golden_dkg.Consensus.Types.f_block_hash = block_hash ;
        Golden_dkg.Consensus.Types.f_signer = signer ;
        Golden_dkg.Consensus.Types.f_partial = partial } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_vote self view block_hash signer partial
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_Timeout { Golden_dkg.Consensus.Types.f_view = view } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_timeout self view
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_NullifyVote
      { Golden_dkg.Consensus.Types.f_view = view ;
        Golden_dkg.Consensus.Types.f_signer = signer ;
        Golden_dkg.Consensus.Types.f_partial = partial } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_nullify_vote self view signer partial
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_FinalizeVote
      { Golden_dkg.Consensus.Types.f_view = view ;
        Golden_dkg.Consensus.Types.f_signer = signer ;
        Golden_dkg.Consensus.Types.f_partial = partial } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_finalize_vote self view signer partial
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_Notarization
      { Golden_dkg.Consensus.Types.f_view = view ;
        Golden_dkg.Consensus.Types.f_block = block ;
        Golden_dkg.Consensus.Types.f_certificate = certificate } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_notarization self view block certificate
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
    | Golden_dkg.Consensus.Types.Message_ProposeRequest
      { Golden_dkg.Consensus.Types.f_view = view ; Golden_dkg.Consensus.Types.f_payload = payload } ->
      let
      (tmp0: t_Replica),
      (out:
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global)) =
        impl_Replica__handle_propose_request self view payload
      in
      let self:t_Replica = tmp0 in
      self, out
      <:
      (t_Replica &
        (Golden_dkg.Consensus.Types.t_StateTransition &
          Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
  in
  self, hax_temp_output
  <:
  (t_Replica &
    (Golden_dkg.Consensus.Types.t_StateTransition &
      Alloc.Vec.t_Vec Golden_dkg.Consensus.Types.t_Outgoing Alloc.Alloc.t_Global))
