# DFINITY vetKeys Reference

Source: https://docs.internetcomputer.org/references/vetkeys-overview
Saved: 2026-02-16

## What is vetKD?

At the core of vetKeys is a cryptographic protocol called verifiably encrypted
threshold Key Derivation (vetKD). The protocol uses threshold cryptography --
the master key is split among multiple nodes. A quorum of nodes must cooperate
to derive new keys. Each node uses its share of the master key to compute an
encrypted share of the derived key. Once enough shares are collected (meeting
the threshold), they can be combined to produce the full derived key.

## Protocol Overview

Three main actors:
- **Subnet nodes**: Execute the key derivation protocol using their master key shares
- **Canisters**: Perform access control and forward user requests via system API
- **Users**: Request derived keys, provide transport public key for secure delivery

### Steps

1. **Transport key generation**: User generates fresh key pair (transport key pair).
   Public key sent to canister for encrypting the derived key.

2. **Access control and routing**: Canister authenticates user, checks authorization,
   then invokes the vetKD system API specifying:
   - Master key ID
   - Transport public key
   - Input (application-specific data for key derivation)
   - Context (domain separation)

3. **Key derivation**: All nodes in the designated vetKD subnet run the threshold
   key derivation protocol:
   - Share computation: Each node computes encrypted share using its master key share
   - Share combination: Once 2f+1 shares available (subnet has 3f+1 nodes),
     shares combined into single encrypted derived key

4. **Response delivery**: Combined encrypted key returned to canister, delivered to user

5. **Verification and decryption**: User verifies key is valid, decrypts using
   private transport key

## System API

### `vetkd_public_key`
Returns the canister's vetKD public key (or a derived subkey if context is provided).

### `vetkd_derive_key`
Derives a vetKey for the given input, encrypted under the provided transport public key.

Parameters:
- `key_id`: Identifies which vetKD master key to use
- `context`: Domain separation (canister ID + optional application context)
- `input`: Application-specific data (identity, key ID, etc.)
- `transport_public_key`: User's ephemeral public key for encryption

Returns: Encrypted vetKey that only the transport key holder can decrypt.

## Master Key Generation

Uses Jens Groth's non-interactive DKG protocol (ePrint 2021/339) with:
- Forward-secure encryption
- Key resharing for membership changes
- High reconstruction threshold (2f+1 out of 3f+1)
- Non-interactive (single communication round)

## Canister Master Keys

Single vetKD master key per subnet, with additive key derivation for per-canister
isolation. Context parameter provides domain separation within each canister.

## References

- vetKeys paper: https://eprint.iacr.org/2023/616
- NCC Group audit: https://www.nccgroup.com/media/251hh3kn/ncc_group_dfinityusaresearch_vetkeys_report_2025-10-08_v10.pdf
- DFINITY vetKeys code: https://github.com/dfinity/vetkeys
- Groth's NI-DKG: https://eprint.iacr.org/2021/339
