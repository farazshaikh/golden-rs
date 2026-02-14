module Golden_rs.Evrf
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec in
  let open Ark_ec.Hashing in
  let open Ark_ec.Hashing.Curve_maps.Wb in
  let open Ark_ec.Hashing.Map_to_curve_hasher in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Field_hashers in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Block_buffer in
  let open Crypto_common in
  let open Digest in
  let open Digest.Core_api in
  let open Digest.Core_api.Ct_variable in
  let open Digest.Core_api.Wrapper in
  let open Generic_array in
  let open Sha2 in
  let open Sha2.Core_api in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// Extract the x-coordinate of an affine point as a scalar in Fr.
/// Per Section 4.2, Evaluate steps 2-3 of the Golden paper (IACR 2025/1924):
/// > "k_0 = S.X -- x-coordinate of S"
/// > "k = int(k_0) -- cast to integer"
/// Converts the Fq x-coordinate (381 bits) to bytes, then reduces mod r
/// into the scalar field. Returns `Fr::zero()` for the identity point.
/// NOTE: Uses Scalar::from(0u64) instead of Scalar::ZERO to avoid
/// arkworks Field::ZERO constant which generates f_ZERO typeclass call
/// in F* extraction. Scalar::from(0u64) uses the From<u64> instance
/// which resolves correctly. See: formal_verification/Implementation.md
let extract_x_as_scalar
      (point: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  if point.Ark_ec.Models.Short_weierstrass.Affine.f_infinity
  then
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 0)
  else
    let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Ark_ff.Biginteger.f_to_bytes_le #(Ark_ff.Biginteger.t_BigInt (mk_usize 6))
        #FStar.Tactics.Typeclasses.solve
        (Ark_ff.Fields.Prime.f_into_bigint #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
            #FStar.Tactics.Typeclasses.solve
            point.Ark_ec.Models.Short_weierstrass.Affine.f_x
          <:
          Ark_ff.Biginteger.t_BigInt (mk_usize 6))
    in
    Ark_ff.Fields.Prime.f_from_le_bytes_mod_order #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Vec.impl_1__as_slice bytes <: t_Slice u8)

/// RFC 9380 compliant hash-to-curve for BLS12-381 G1.
/// Corresponds to the random oracles `H_{G_in,1}` and `H_{G_in,2}` from
/// Section 4.1 of the Golden paper (IACR 2025/1924). The `domain` parameter
/// provides domain separation between the two hash functions.
/// Implements the `BLS12381G1_XMD:SHA-256_SSWU_RO_` suite using arkworks'
/// `MapToCurveBasedHasher` with the Wahby-Boneh (WB) map. This produces
/// uniformly distributed points on the curve per the IETF standard.

(* hash_to_curve: replaced with assume val to avoid complex Typenum/Digest
   type nesting that causes F* parsing issues. Treated as a random oracle
   in all proofs (matches the Lean specification in EVRFSymmetry.lean). *)
assume val hash_to_curve (domain msg: t_Slice u8)
    : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config

let derive_pad
      (sk:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (peer_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      (msg: t_Slice u8)
      (beta:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
      Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config) =
  let s:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          peer_pk
          sk
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let k:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    extract_x_as_scalar s
  in
  let h1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    hash_to_curve ((let list =
            [
              mk_u8 103; mk_u8 111; mk_u8 108; mk_u8 100; mk_u8 101; mk_u8 110; mk_u8 45; mk_u8 101;
              mk_u8 118; mk_u8 114; mk_u8 102; mk_u8 45; mk_u8 104; mk_u8 49
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 14);
          Rust_primitives.Hax.array_of_list 14 list)
        <:
        t_Slice u8)
      msg
  in
  let h2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    hash_to_curve ((let list =
            [
              mk_u8 103; mk_u8 111; mk_u8 108; mk_u8 100; mk_u8 101; mk_u8 110; mk_u8 45; mk_u8 101;
              mk_u8 118; mk_u8 114; mk_u8 102; mk_u8 45; mk_u8 104; mk_u8 50
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 14);
          Rust_primitives.Hax.array_of_list 14 list)
        <:
        t_Slice u8)
      msg
  in
  let t1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          h1
          k
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let t2:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          h2
          k
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  let r1:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    extract_x_as_scalar t1
  in
  let r2:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    extract_x_as_scalar t2
  in
  let r:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Ops.Arith.f_add #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          beta
          r1
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      r2
  in
  let r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
  =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          (Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                Ark_bls12_381_.Curves.G1.t_Config)
              #FStar.Tactics.Typeclasses.solve
              ()
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
          r
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)
  in
  r, r_commitment
  <:
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) &
    Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
