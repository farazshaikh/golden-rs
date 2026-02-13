---
name: Key Refresh Implementation
overview: "Implement Golden's key refresh protocol (proactive secret sharing via zero secret sharing) where participants rotate their secret shares while keeping the global sk and PK unchanged. Per the paper Section 5.2: set omega_i = 0 and verify A_{j,0} is the identity. Note: the paper calls this 'key resharing' but it is more precisely 'key refresh' since the group and (n,t) stay the same."
todos:
  - id: reshare-protocol
    content: Add round0_refresh + round1_refresh to protocol.rs (omega=0, verify A_{j,0}==identity)
    status: pending
  - id: reshare-node
    content: Add run_refresh method to Node in node.rs
    status: pending
  - id: reshare-test
    content: "Add refresh test to main.rs: run refresh, verify PK unchanged, new shares different, all C(5,3) reconstruct same sk"
    status: pending
isProject: false
---

# Key Refresh Implementation

## Paper Reference (Section 5.2, "Key Resharing")

> Golden can be adapted to support distributed key resharing, where participants rotate their secret shares sk_i, but where the group keys sk and PK remain the same. The common technique to doing so is using zero secret sharing, where participants perform the protocol as defined in Figure 4, with the following changes:
>
> 1. Instead of sampling omega_i at random, each participant sets **omega_i = 0**
> 2. Each participant performs one additional check in Round1, checking that **A_{j,0} equals the identity** of the group for all j (verifying f_j(0) = 0)

**Terminology note:** The paper calls this "key resharing" but in the broader literature this is more precisely called **key refresh** or **proactive secret sharing** -- the group membership and (n, t) parameters stay the same, only the shares rotate. True "resharing" typically refers to transferring the secret to a different group with different (n', t').

## Changes

### 1. `protocol.rs` -- Add `round0_refresh` and `round1_refresh`

`**round0_refresh**`: Identical to `round0` except `omega = Scalar::ZERO` instead of `Scalar::rand(rng)`. Can be implemented by extracting a shared helper or by adding a boolean parameter, but a separate function is cleaner.

`**round1_refresh**`: Identical to `round1` except:

- Before decryption, verify that `A_{j,0} == G1Affine::identity()` for every received message (and for own commitment). If any A_{j,0} is not the identity, return a new error variant `ZeroSecretViolation`.
- The `public_key` derivation step should still compute PK from commitments, but since all A_{j,0} are identity, the PK contribution from the refresh is the identity -- the caller provides the original PK to carry forward.

Both functions accept `existing_share: Scalar` (the node's current sk_i from the initial DKG) so the output `secret_share` = `existing_share + sum of new zero-sharing deltas`.

### 2. `protocol.rs` -- Add error variant

Add `ZeroSecretViolation { sender: NodeId }` to `ProtocolError`.

### 3. `node.rs` -- Add `run_refresh` method

```
pub async fn run_refresh(mut self, existing_output: DkgOutput) -> DkgOutput
```

Same flow as `run()` but calls `round0_refresh` / `round1_refresh`. The output `DkgOutput` has the same `public_key` as before but fresh `secret_share` and `public_key_shares`.

### 4. `main.rs` -- Add refresh test after initial DKG

After the initial DKG passes all checks:

1. Print a separator for the refresh phase
2. Create a fresh `Network`, spawn n nodes with the same identity keys and beta
3. Each node runs `run_refresh` carrying its existing `DkgOutput`
4. Verify:
  - PK is unchanged from the initial DKG
  - New shares are DIFFERENT from old shares (rotation happened)
  - All C(5,3) combinations of new shares reconstruct the same sk
  - `g^sk == PK` (same PK as before)

### Key insight for the test

After refreshing, each node's new share is `old_sk_i + delta_i` where `delta_i = sum_j f_j(i)` with all `f_j(0) = 0`. Since the deltas are from zero-sharing polynomials, `sum delta_i * L_i(0) = 0`, so Lagrange interpolation of the new shares still recovers the same `sk`.

## Files modified

- `[src/protocol.rs](/wrk/tmt/goldenkeysharing/src/protocol.rs)` -- `round0_refresh`, `round1_refresh`, new error variant
- `[src/node.rs](/wrk/tmt/goldenkeysharing/src/node.rs)` -- `run_refresh` method
- `[src/main.rs](/wrk/tmt/goldenkeysharing/src/main.rs)` -- refresh phase after initial DKG
