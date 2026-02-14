module Ark_ff.Biginteger

open Rust_primitives

/// BigInt type used by arkworks for field element internal representation.
assume new type t_BigInt (n : usize) : Type0

/// Convert BigInt to little-endian bytes.
class t_BigInteger (v_Self : Type0) = {
  f_to_bytes_le_pre : v_Self -> Type0;
  f_to_bytes_le_post : v_Self -> Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> Type0;
  f_to_bytes_le : x0: v_Self
    -> Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
       (f_to_bytes_le_pre x0) (fun result -> f_to_bytes_le_post x0 result);
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_bigint (n : usize) : t_BigInteger (t_BigInt n)

/// f_to_bits_le: hax calls with #type #solve value
assume val f_to_bits_le : #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst:t_BigInteger a
  -> a -> Alloc.Vec.t_Vec bool Alloc.Alloc.t_Global
