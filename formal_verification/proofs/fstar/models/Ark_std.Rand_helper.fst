module Ark_std.Rand_helper

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// arkworks UniformRand trait -- generates a random field element.
///
/// In the extracted code, this appears as:
///   Ark_std.Rand_helper.f_rand #(t_Fp ...) #solve #rng_type rng
///
/// We model this as an opaque function returning an arbitrary element.

class t_UniformRand (v_Self : Type0) = {
  f_rand : (#rng_t: Type0) -> rng: rng_t -> (rng_t & v_Self);
}

/// Instance for t_Fp -- random field element generation.
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_uniform_rand_fp (config : Type0) (n : usize) :
  t_UniformRand (t_Fp (t_MontBackend config n) n)
