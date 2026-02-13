module Golden_rs.Reshare_node
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// An old group member participating in resharing.
/// Deals its existing share to the new group via eVRF-encrypted broadcast.
/// After dealing, the old node's role is complete -- it does not produce
/// a [`DkgOutput`].
type t_OldReshareNode = {
  f_id:u32;
  f_sk_identity:Golden_rs.Types.t_SecretScalar;
  f_e_pk_identity:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_old_share:Golden_rs.Types.t_SecretScalar;
  f_tt_new:u32;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_network:Golden_rs.Reshare_network.t_ReshareNetwork;
  f_e_n_old:u32;
  f_e_receiver:Tokio.Sync.Broadcast.t_Receiver Golden_rs.Types.t_ReshareMsg
}

/// Create a new old-group reshare node and register with the network.
/// Generates an identity keypair and registers with proof of knowledge.
let impl_OldReshareNode__new
      (id: u32)
      (old_share:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (tt_new: u32)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (n_old: u32)
      (network: Golden_rs.Reshare_network.t_ReshareNetwork)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Deal old share to new group and return.
/// Waits for all participants to register, then creates a dealing polynomial
/// `g_i(0) = old_share` and broadcasts encrypted evaluations to the new group.
let impl_OldReshareNode__run (self: t_OldReshareNode) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// A new group member participating in resharing.
/// Receives deals from old members and computes a new secret key share.
/// The output preserves the original public key `PK` and produces shares
/// under the new group's `(n_new, t_new)` parameters.
type t_NewReshareNode = {
  f_id:u32;
  f_sk_identity:Golden_rs.Types.t_SecretScalar;
  f_e_pk_identity:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_beta:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_original_pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_old_pk_shares:Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Std.Hash.Random.t_RandomState;
  f_tt_old:u32;
  f_n_old:u32;
  f_network:Golden_rs.Reshare_network.t_ReshareNetwork;
  f_receiver:Tokio.Sync.Broadcast.t_Receiver Golden_rs.Types.t_ReshareMsg
}

/// Create a new new-group reshare node and register with the network.
/// Generates an identity keypair and registers with proof of knowledge.
let impl_NewReshareNode__new
      (id: u32)
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
      (tt_old n_old: u32)
      (network: Golden_rs.Reshare_network.t_ReshareNetwork)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

/// Collect reshare messages from old nodes and compute new share.
/// Waits for `n_old` messages, then runs [`reshare::reshare_receive`] to
/// verify, decrypt, and aggregate into a new [`DkgOutput`].
let impl_NewReshareNode__run (self: t_NewReshareNode) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""
