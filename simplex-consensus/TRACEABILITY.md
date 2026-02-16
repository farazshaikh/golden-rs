# Simplex Consensus -- Paper-to-Code Traceability

Maps every protocol element in the Simplex paper (Chan & Pass 2023,
Section 2) to the corresponding line in `simplex-consensus/src/`.

Reference: <https://eprint.iacr.org/2023/463.pdf>

---

## Data Structures (Paper Section 2, pages 8-9)

| Paper Concept | Paper Quote | Code Location |
|---|---|---|
| Block | "A block b is a tuple (h, parent, txs)" | `types.rs:25-38` -- `struct Block { view, parent_hash, payload, proposer }` |
| Block height h | "h is the height of the block" | `types.rs:29` -- `Block.view: View` (view = height) |
| Parent hash | "parent is the hash of a parent blockchain" | `types.rs:32` -- `Block.parent_hash: BlockHash` |
| Transactions | "txs is an arbitrary sequence of strings" | `types.rs:35` -- `Block.payload: Vec<u8>` |
| Genesis block | "b_0 := (0, empty, empty)" | `types.rs:254-261` -- `ChainState::genesis()` with `tip_hash: [0u8; 32]` |
| Dummy block | "The special dummy block ⊥_h := (h, ⊥, ⊥)" | `replica.rs:507` -- sentinel `[0u8; 32]` for `notarized_in_view` |
| Blockchain | "(b_0, b_1, ..., b_h) such that b_0 is genesis" | Implicit in `ChainState.tip_hash` -- only the tip is tracked |
| Notarization | "A set of signed <vote, h, b> from >= 2n/3 processes" | `replica.rs:425-492` -- `try_notarize()`, threshold check at line 442 |
| Notarized blockchain | "(b_0,...,b_h, S) where S is notarizations for each block" | `types.rs:42-46` -- `CertKind::Notarization(BlockHash)` |
| Finalization | "A set of signed <finalize, h> from >= 2n/3 processes" | `replica.rs:526-543` -- `try_finalize()`, threshold check at line 532 |
| Finalized block | "Notarized and accompanied by a finalization for h" | `types.rs:51-53` -- `CertKind::Finalization(BlockHash)` |
| Certificate | Combined threshold BLS signature | `types.rs:57-63` -- `struct Certificate { view, kind, signature }` |
| Block hash | "H : collision-resistant hash function" | `types.rs:267-278` -- `fn block_hash()` using SHA-256 |

## Leader Election (Paper Section 2.1, page 9)

| Paper Concept | Paper Quote | Code Location |
|---|---|---|
| Leader oracle | "L_h := H*(h) mod n" | `vrf.rs:30-34` -- `fn elect_leader(vrf_seed, n) -> NodeId` |
| VRF message | "H*(h) where H* is a public hash function" | `vrf.rs:18-22` -- `fn vrf_message(view) -> Vec<u8>` |
| Leader check | "On seeing the first proposal from L_h" | `replica.rs:219-221` -- `if block.proposer != leader { Rejected(WrongLeader) }` |

## Protocol Steps (Paper Section 2.1, pages 9-10)

### Step 1: Leader Proposal

| Paper Quote | Code Location |
|---|---|
| "If p = L_h, p multicasts a single proposal" | `replica.rs:155-197` -- `handle_propose_request()` |
| "b_0,...,b_h is p's choice of a blockchain" | `replica.rs:178-183` -- block built from `self.chain_state.tip_hash` |
| "b_h != ⊥_h" (non-dummy) | Implicit: `ProposeRequest` always produces a real block |
| Leader proposal broadcast | `replica.rs:194` -- returns `Outgoing::Proposal { block }` |

### Step 2: Dummy Blocks (Timeout)

| Paper Quote | Code Location |
|---|---|
| "Each process starts timer T_h, set to fire after 3Δ" | Timer is external; `Message::Timeout { view }` triggers it |
| "If T_h fires, vote for dummy by multicasting <vote, h, ⊥_h>" | `replica.rs:257-289` -- `handle_timeout()` |
| Timer fired flag | `replica.rs:273` -- `self.timer_fired = true` |
| Dummy vote sent flag | `replica.rs:274` -- `self.dummy_sent = true` |
| Produce dummy vote | `replica.rs:276-282` -- `sign_dummy()` -> `Outgoing::NullifyVote` |
| Threshold check for dummy | `replica.rs:285` -- calls `try_nullify()` |

### Step 3: Notarizing Block Proposals

| Paper Quote | Code Location |
|---|---|
| "On seeing the FIRST proposal from L_h" | `replica.rs:199-255` -- `handle_proposal()` |
| "check that b_h != ⊥_h" | Implicit: `Message::Proposal` always has a real block |
| "check that b_0,...,b_h is a valid blockchain" | `replica.rs:229-231` -- `if block.parent_hash != self.chain_state.tip_hash` |
| "check that (b_0,...,b_{h-1}, S) is notarized" | Simplified: parent_hash match implies valid notarized parent |
| "If all checks pass, multicast <vote, h, b_h>" | `replica.rs:233-248` -- `sign_vote()` -> `Outgoing::Vote` |
| One vote per iteration | `replica.rs:224-227` -- `if self.voted_in_view { Rejected(AlreadyVoted) }` |
| Only vote for L_h's proposal | `replica.rs:218-221` -- `if block.proposer != leader { Rejected(WrongLeader) }` |
| Store block for later notarization | `replica.rs:216` -- `self.known_blocks.insert(block_hash, block)` |

### Step 4: Next Iteration and Finalize Votes

| Paper Quote | Code Location |
|---|---|
| "On seeing a notarized blockchain of height h, enter h+1" | `replica.rs:429-492` -- `try_notarize()` calls `advance_view()` at line 489 |
| "Also enter h+1 on seeing relayed notarization" | `replica.rs:374-421` -- `handle_notarization()` calls `advance_view()` at line 418 |
| "p multicasts its view of the notarized blockchain" | `replica.rs:482-486` -- `Outgoing::RelayNotarization` |
| "If timer T_h did NOT fire yet: cancel T_h" | `replica.rs:457` -- `if !self.timer_fired && !self.finalize_sent` |
| "multicast <finalize, h>" | `replica.rs:459-461` -- `sign_finalize()` -> `Outgoing::FinalizeVote` |

### Step 5: Finalized Outputs

| Paper Quote | Code Location |
|---|---|
| "Whenever p sees a finalized blockchain, output LOG" | `replica.rs:526-543` -- `try_finalize()` returns `StateTransition::Finalized` |
| "Finalized = notarized + 2n/3 finalize messages" | `replica.rs:532` -- `if self.finalize_votes.len() < threshold { Pending }` |
| Increment finalized count | `replica.rs:537` -- `self.chain_state.finalized_count += 1` |

## Safety Invariants (Paper Section 2.2 + Lemmas 3.2, 3.3)

| Paper Lemma | What It Guarantees | Code Enforcement |
|---|---|---|
| **Lemma 3.2** | Two distinct non-dummy blocks CANNOT both be notarized at height h (with f < n/3) | `replica.rs:50-51` -- `voted_in_view: bool` ensures one vote per iteration. `replica.rs:224-227` -- rejects if already voted. |
| **Lemma 3.3** | If height h is finalized, dummy ⊥_h CANNOT be notarized | `replica.rs:55-58` -- `finalize_sent` and `dummy_sent` flags. `replica.rs:267-271` -- `handle_timeout` returns Pending if `finalize_sent \|\| dummy_sent`. This ensures a node NEVER sends both `<finalize, h>` and `<vote, h, ⊥_h>`. |
| **Theorem 3.1** (Consistency) | If Alice finalizes chain ending at h, and Bob finalizes a longer chain, Alice's is a prefix of Bob's | Follows from Lemmas 3.2 + 3.3 + collision-resistant `block_hash()` |

## Liveness (Paper Section 3.3, Lemmas 3.4-3.6)

| Paper Lemma | What It Guarantees | Simulation Model |
|---|---|---|
| **Lemma 3.4** (Sync) | If one honest enters h by time t, all enter by t+δ | Engine delivers messages synchronously in each view |
| **Lemma 3.5** (Honest Leader) | Honest leader's block finalized by t+3δ | `handle_propose_request` -> votes -> `try_notarize` -> `FinalizeVote` -> `try_finalize` |
| **Lemma 3.6** (Faulty Leader) | All honest enter h+1 by t+3Δ+δ | Engine sends `Message::Timeout` to stuck replicas at end of view |

## VRF Seed Derivation

| Event | VRF Seed Source | Code Location |
|---|---|---|
| Block notarized | Combined threshold signature on `<vote, h, b_h>` | `replica.rs:477-480` -- `beacon::derive_randomness` from combined sig |
| Dummy notarized | Combined threshold signature on `<vote, h, ⊥_h>` | `replica.rs:509-516` -- same derivation from nullify votes |
| Leader election | `SHA-256(vrf_seed) mod n + 1` | `vrf.rs:30-34` -- `elect_leader()` |

## Capitulation (f+1 Byzantine -- Outside Paper's Threat Model)

The paper proves safety only for f < n/3. Our `Capitulation` scenario
uses f+1 Byzantine nodes to demonstrate what breaks:

| Paper Guarantee | What Breaks | How |
|---|---|---|
| Lemma 3.2 (no two notarized blocks) | TWO blocks both notarized | 4 capitulators double-vote: each partition gets 3 honest + 4 capitulators = 7 >= t |
| Consistency (Theorem 3.1) | Honest nodes finalize different blocks | Partition A finalizes block A, partition B finalizes block B |
| Liveness (Theorem 3.4) | Chain permanently stalls | After fork, each leader proposes from its own tip; the other partition rejects (BadParentHash) |

## Message Flow Summary

```
ProposeRequest -> Replica (leader) -> Outgoing::Proposal + Outgoing::Vote
    |
    v
Message::Proposal -> Replica (voter) -> Outgoing::Vote
    |
    v
Message::Vote -> Replica (accumulate) -> [threshold reached] -> Outgoing::FinalizeVote + Outgoing::RelayNotarization
    |                                                                    |
    v                                                                    v
Message::FinalizeVote -> Replica (accumulate) -> [threshold]   Message::Notarization -> Replica -> advance_view
    |
    v
StateTransition::Finalized

OR (timeout path):

Message::Timeout -> Replica -> Outgoing::NullifyVote
    |
    v
Message::NullifyVote -> Replica (accumulate) -> [threshold reached] -> StateTransition::Nullified -> advance_view
```
