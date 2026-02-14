module Ark_ec.Models.Short_weierstrass.Affine

open Rust_primitives

/// Affine point on a short Weierstrass curve (x, y, infinity flag).
/// In arkworks: `ark_ec::models::short_weierstrass::Affine<P>`.
/// Must be a record type so F* can project fields like f_x and f_infinity.

noeq type t_Affine (config : Type0) = {
  f_x : Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6);
  f_y : Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
      Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6);
  f_infinity : bool;
}
