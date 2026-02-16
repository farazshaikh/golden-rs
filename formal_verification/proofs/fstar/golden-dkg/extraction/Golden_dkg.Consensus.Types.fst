module Golden_dkg.Consensus.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Block_buffer in
  let open Digest in
  let open Digest.Core_api in
  let open Digest.Core_api.Ct_variable in
  let open Digest.Core_api.Wrapper in
  let open Digest.Digest in
  let open Generic_array in
  let open Sha2.Core_api in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// A consensus block proposed by a leader in a given view.
/// Paper (Section 2, page 8): "A block b is a tuple (h, parent, txs),
/// where h is the height, parent is the hash of a parent blockchain,
/// and txs is an arbitrary sequence of strings."
/// We add `proposer` to identify the leader who created the block.
type t_Block = {
  f_view:u64;
  f_parent_hash:t_Array u8 (mk_usize 32);
  f_payload:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_proposer:u32
}

let impl_1: Core_models.Clone.t_Clone t_Block =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_Block

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Marker.t_StructuralPartialEq t_Block

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Cmp.t_PartialEq t_Block t_Block

unfold
let impl_4 = impl_4'

/// The kind of certificate produced in a view.
/// Paper (Section 2, pages 8-9): The protocol produces three kinds of
/// quorum certificates, each requiring >= 2n/3 signed messages.
type t_CertKind =
  | CertKind_Notarization : t_Array u8 (mk_usize 32) -> t_CertKind
  | CertKind_Nullification : t_CertKind
  | CertKind_Finalization : t_Array u8 (mk_usize 32) -> t_CertKind

let impl_5: Core_models.Clone.t_Clone t_CertKind =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Fmt.t_Debug t_CertKind

unfold
let impl_6 = impl_6'

/// A threshold BLS certificate (combined from >= 2f+1 partial signatures).
/// Paper: certificates are sets of 2n/3 signed messages. We use threshold
/// BLS signatures so the certificate is a single combined G2 point.
type t_Certificate = {
  f_view:u64;
  f_kind:t_CertKind;
  f_signature:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
}

let impl_7: Core_models.Clone.t_Clone t_Certificate =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Fmt.t_Debug t_Certificate

unfold
let impl_8 = impl_8'

/// A message that a Replica can receive from the network (or local timer).
/// These correspond to the protocol steps in Paper Section 2.1 (pages 9-10).
/// # Paper-to-Code Mapping (Protocol Messages)
/// | Paper Message | Variant |
/// |---------------|---------|
/// | `<propose, h, b_0..b_h, S>` (Step 1) | [`Proposal`](Message::Proposal) |
/// | `<vote, h, b_h>` (Step 3) | [`Vote`](Message::Vote) |
/// | `<vote, h, ⊥_h>` (Step 2, timer fires) | [`NullifyVote`](Message::NullifyVote) |
/// | Timer T_h fires (Step 2) | [`Timeout`](Message::Timeout) |
/// | `<finalize, h>` (Step 4) | [`FinalizeVote`](Message::FinalizeVote) |
/// | Relayed notarized blockchain (Step 4) | [`Notarization`](Message::Notarization) |
/// | "If p = L_h, propose" (Step 1) | [`ProposeRequest`](Message::ProposeRequest) |
type t_Message =
  | Message_Proposal { f_block:t_Block }: t_Message
  | Message_Vote {
    f_view:u64;
    f_block_hash:t_Array u8 (mk_usize 32);
    f_signer:u32;
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Message
  | Message_Timeout { f_view:u64 }: t_Message
  | Message_NullifyVote {
    f_view:u64;
    f_signer:u32;
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Message
  | Message_FinalizeVote {
    f_view:u64;
    f_signer:u32;
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Message
  | Message_Notarization {
    f_view:u64;
    f_block:t_Block;
    f_certificate:t_Certificate
  }: t_Message
  | Message_ProposeRequest {
    f_view:u64;
    f_payload:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
  }: t_Message

let impl_9: Core_models.Clone.t_Clone t_Message =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Fmt.t_Debug t_Message

unfold
let impl_10 = impl_10'

/// Why a proposal was rejected by this replica.
/// Each reason corresponds to a validation check in Paper Section 2.1, Step 3.
type t_RejectReason =
  | RejectReason_WrongLeader : t_RejectReason
  | RejectReason_BadParentHash : t_RejectReason
  | RejectReason_WrongView : t_RejectReason
  | RejectReason_AlreadyVoted : t_RejectReason

/// The state transition produced by a Replica after processing a Message.
/// # Paper-to-Code Mapping (State Transitions)
/// | Paper Concept | Variant |
/// |---------------|---------|
/// | "A notarized block" (>= 2n/3 votes) | [`Notarized`](StateTransition::Notarized) |
/// | "A finalized block" (notarized + >= 2n/3 finalize) | [`Finalized`](StateTransition::Finalized) |
/// | Notarized dummy block ⊥_h | [`Nullified`](StateTransition::Nullified) |
type t_StateTransition =
  | StateTransition_Notarized {
    f_view:u64;
    f_block_hash:t_Array u8 (mk_usize 32)
  }: t_StateTransition
  | StateTransition_Finalized {
    f_view:u64;
    f_block_hash:t_Array u8 (mk_usize 32)
  }: t_StateTransition
  | StateTransition_Nullified { f_view:u64 }: t_StateTransition
  | StateTransition_Rejected {
    f_view:u64;
    f_reason:t_RejectReason
  }: t_StateTransition
  | StateTransition_Pending : t_StateTransition

let impl_11: Core_models.Clone.t_Clone t_StateTransition =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Fmt.t_Debug t_StateTransition

unfold
let impl_12 = impl_12'

let t_RejectReason_cast_to_repr (x: t_RejectReason) : isize =
  match x <: t_RejectReason with
  | RejectReason_WrongLeader  -> mk_isize 0
  | RejectReason_BadParentHash  -> mk_isize 1
  | RejectReason_WrongView  -> mk_isize 2
  | RejectReason_AlreadyVoted  -> mk_isize 3

let impl_13: Core_models.Clone.t_Clone t_RejectReason =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Fmt.t_Debug t_RejectReason

unfold
let impl_14 = impl_14'

/// An outgoing message that the Replica wants to broadcast.
/// The caller (engine / network layer) delivers these to other replicas.
/// # Paper-to-Code Mapping (Outgoing Messages)
/// | Paper Action | Variant |
/// |-------------|---------|
/// | "multicast `<vote, h, b_h>`" (Step 3) | [`Vote`](Outgoing::Vote) |
/// | "multicast `<vote, h, ⊥_h>`" (Step 2) | [`NullifyVote`](Outgoing::NullifyVote) |
/// | "multicast `<finalize, h>`" (Step 4) | [`FinalizeVote`](Outgoing::FinalizeVote) |
/// | "multicasts notarized blockchain" (Step 4) | [`RelayNotarization`](Outgoing::RelayNotarization) |
/// | "multicasts proposal" (Step 1) | [`Proposal`](Outgoing::Proposal) |
type t_Outgoing =
  | Outgoing_Vote {
    f_view:u64;
    f_block_hash:t_Array u8 (mk_usize 32);
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Outgoing
  | Outgoing_NullifyVote {
    f_view:u64;
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Outgoing
  | Outgoing_FinalizeVote {
    f_view:u64;
    f_partial:Golden_dkg.Threshold.Types.t_PartialSignature
  }: t_Outgoing
  | Outgoing_RelayNotarization {
    f_view:u64;
    f_block:t_Block;
    f_certificate:t_Certificate
  }: t_Outgoing
  | Outgoing_Proposal { f_block:t_Block }: t_Outgoing

let impl_15: Core_models.Clone.t_Clone t_Outgoing =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Fmt.t_Debug t_Outgoing

unfold
let impl_16 = impl_16'

/// Network configuration: public parameters for all replicas.
/// Paper (Section 2, page 8): "a bare PKI" setup where each process has
/// a keypair and all public keys are known.
type t_NetworkConfig = {
  f_n:u32;
  f_t:u32;
  f_f:u32;
  f_group_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
}

let impl_17: Core_models.Clone.t_Clone t_NetworkConfig =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

/// Tracks the local chain state of a replica across views.
/// Paper: Each process "keeps track of which iteration h it is currently in,
/// and also stores all of the notarized blocks and messages that it has seen."
/// We simplify to just the tip hash, VRF seed, and counters.
type t_ChainState = {
  f_tip_hash:t_Array u8 (mk_usize 32);
  f_vrf_seed:t_Array u8 (mk_usize 32);
  f_finalized_count:u64;
  f_nullified_count:u64
}

let impl_18: Core_models.Clone.t_Clone t_ChainState =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': Core_models.Fmt.t_Debug t_ChainState

unfold
let impl_19 = impl_19'

/// Create the genesis chain state.
/// Paper: "Define the genesis block to be b_0 := (0, empty, empty)."
let impl_ChainState__genesis (_: Prims.unit) : t_ChainState =
  {
    f_tip_hash = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32);
    f_vrf_seed = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32);
    f_finalized_count = mk_u64 0;
    f_nullified_count = mk_u64 0
  }
  <:
  t_ChainState

/// Compute the SHA-256 hash of a block.
/// Paper: "H : {0,1}* -> {0,1}* is a collision-resistant hash function."
/// Used to chain blocks (parent_hash) and identify blocks in certificates.
let block_hash (block: t_Block) : t_Array u8 (mk_usize 32) =
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
      (Core_models.Num.impl_u64__to_be_bytes block.f_view <: t_Array u8 (mk_usize 8))
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
      #(t_Array u8 (mk_usize 32))
      hasher
      block.f_parent_hash
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
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      hasher
      block.f_payload
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
      #(t_Array u8 (mk_usize 4))
      hasher
      (Core_models.Num.impl_u32__to_be_bytes block.f_proposer <: t_Array u8 (mk_usize 4))
  in
  let result:Generic_array.t_GenericArray u8
    (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
        Typenum.Bit.t_B0) =
    Digest.Digest.f_finalize #(Digest.Core_api.Wrapper.t_CoreWrapper
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
  in
  let hash:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let hash:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      hash
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
          result
        <:
        t_Slice u8)
  in
  hash
