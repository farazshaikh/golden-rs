module Golden_rs.Node
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// A participant in the Golden DKG protocol.
/// Holds the node's identity keypair `(sk_i^I, PK_i^I)`, protocol parameters
/// `(n, t, beta)`, and the network handle for broadcast communication.
type t_Node = {
  f_id:u32;
  f_n:u32;
  f_t:u32;
  f_sk:Golden_rs.Types.t_SecretScalar;
  f_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_network:Golden_rs.Network.t_Network;
  f_receiver:Tokio.Sync.Broadcast.t_Receiver Golden_rs.Types.t_Round0Msg
}

/// Create a new node and register it with the network.
/// Per Section 5.1 of the Golden paper (IACR 2025/1924), generates an
/// identity keypair `(sk_i^I, PK_i^I)` and registers the public key with
/// the PKI via a Schnorr proof of knowledge (Appendix F).
let impl_Node__new
      (id n t: u32)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (network: Golden_rs.Network.t_Network)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Run the full DKG protocol (Round 0 + Round 1 per Figure 4).
/// 1. Wait for all nodes to register
/// 2. Execute Round 0: generate and broadcast
/// 3. Collect `n-1` Round 0 messages from peers
/// 4. Execute Round 1: verify, decrypt, aggregate
/// 5. Return [`DkgOutput`] containing `(PK, {PK_j}, sk_i)`
let impl_Node__run (self: t_Node) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Run the key refresh protocol (zero secret sharing).
/// Per Section 5.2 of the Golden paper (IACR 2025/1924): rotates secret
/// shares while keeping `sk` and `PK` unchanged. Each node uses `omega = 0`
/// and the zero-sharing deltas update existing shares.
let impl_Node__run_refresh (self: t_Node) (existing_output: Golden_rs.Types.t_DkgOutput)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""
