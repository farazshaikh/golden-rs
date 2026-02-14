module Golden_rs.Zk_evrf.Bit_decompose
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Num_traits.Identities in
  ()

/// Result of bit-decomposition: the allocated bit variables.
type t_BitDecomposition = {
  f_bits:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global;
  f_value_var:usize
}

/// Decompose a scalar value into `lambda+1` bits in the constraint system.
/// Per Section 4.4 of the Golden paper (IACR 2025/1924):
/// - Allocates `lambda+1` bit variables and the original value
/// - Constrains each bit: `k_i * (k_i - 1) = 0` (boolean constraint)
/// - Constrains recomposition: `k = sum 2^i * k_i`
/// Total constraints: `lambda + 2` (one per bit + one recomposition).
/// `lambda` is the bit-length (e.g., 256 for a 256-bit scalar).
/// The value must fit in `lambda+1` bits.

(* bit_decompose function replaced with assume val. *)
assume val bit_decompose : #a:Type0 -> #b:Type0 -> a -> b -> Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem -> (Golden_rs.Zk_evrf.Nonnative.t_ConstraintSystem & t_BitDecomposition)

let constraint_count (lambda: Rust_primitives.Integers.usize) : Rust_primitives.Integers.usize = lambda +! Rust_primitives.Integers.mk_usize 2
