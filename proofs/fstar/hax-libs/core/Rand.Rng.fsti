module Rand.Rng

/// PATCHED: Added t_Rng typeclass + f_fill (upstream is empty).
/// Needed by Ark_std.Rand_helper and Golden_rs.Shamir/Protocol/Reshare extraction.

class t_Rng (v_Self : Type0) = {
  __rng_dummy : unit;
}

/// f_fill: fill a byte buffer with random data.
/// Extracted code calls: Rand.Rng.f_fill #rng_type #solve #buf_type rng buf
/// Returns (updated_rng, filled_buf).
val f_fill (#v_Self: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_Rng v_Self)
  (#v_Buf: Type0)
  (rng: v_Self) (buf: v_Buf)
  : (v_Self & v_Buf)
