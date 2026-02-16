module Ark_ff.Fields.Prime

open Rust_primitives

/// PrimeField trait operations: into_bigint, from_le_bytes_mod_order.

class t_PrimeField (v_Self : Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method] f_BigIntN : Rust_primitives.Integers.usize;
  f_into_bigint_pre : v_Self -> Type0;
  f_into_bigint_post : v_Self -> Ark_ff.Biginteger.t_BigInt f_BigIntN -> Type0;
  f_into_bigint : x0: v_Self
    -> Prims.Pure (Ark_ff.Biginteger.t_BigInt f_BigIntN)
       (f_into_bigint_pre x0) (fun result -> f_into_bigint_post x0 result);
  f_from_le_bytes_mod_order_pre : t_Slice u8 -> Type0;
  f_from_le_bytes_mod_order_post : t_Slice u8 -> v_Self -> Type0;
  f_from_le_bytes_mod_order : x0: t_Slice u8
    -> Prims.Pure v_Self
       (f_from_le_bytes_mod_order_pre x0) (fun result -> f_from_le_bytes_mod_order_post x0 result);
}

/// Instance for Fr (scalar field)
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_prime_field_fr (config : Type0) (n : usize) :
  t_PrimeField (t_Fp (t_MontBackend config n) n)
