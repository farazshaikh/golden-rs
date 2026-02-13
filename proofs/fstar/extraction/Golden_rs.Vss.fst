module Golden_rs.Vss
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  ()

/// Generate a Feldman VSS commitment for a polynomial.
/// Per Section 3.2 of the Golden paper (IACR 2025/1924):
/// > "C_k = g^{a_k} for each coefficient a_k"
/// Returns a vector of `g^{a_k}` for each coefficient `a_k` in the polynomial.
/// The first element `C_0 = g^{a_0}` is a commitment to the secret itself.
let commit (poly: Golden_rs.Shamir.t_Polynomial)
    : Alloc.Vec.t_Vec
      (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      Alloc.Alloc.t_Global =
  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Slice.Iter.t_Iter
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (
              Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
            -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec
        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        Alloc.Alloc.t_Global)
    (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        #(
              Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
            -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
        (Core_models.Slice.impl__iter #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            (Alloc.Vec.impl_1__as_slice poly.Golden_rs.Shamir.f_coefficients
              <:
              t_Slice
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          <:
          Core_models.Slice.Iter.t_Iter
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (fun coeff ->
            let coeff:Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
              coeff
            in
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
                    Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  coeff
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
            <:
            Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      <:
      Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Slice.Iter.t_Iter
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (
              Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
            -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))

/// Verify that a share is consistent with a VSS commitment.
/// Per Section 3.2 of the Golden paper (IACR 2025/1924), checks the
/// verification equation:
/// > "g^{f(j)} == product_{k=0}^{t-1} C_k^{j^k}"
/// Returns `true` if `g^{share}` equals the product of `C_k^{index^k}` over
/// all commitment elements, confirming the share lies on the committed polynomial.
let verify_share
      (commitment:
          t_Slice
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (index: u32)
      (share:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : bool =
  let x:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (cast (index <: u32) <: u64)
  in
  let expected:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
  =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let x_pow:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 1)
  in
  let
  (expected: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
  (x_pow:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          #FStar.Tactics.Typeclasses.solve
          commitment
        <:
        Core_models.Slice.Iter.t_Iter
        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (expected, x_pow
        <:
        (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (fun temp_0_ c_k ->
          let
          (expected:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
          (x_pow:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
            temp_0_
          in
          let c_k:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
          =
            c_k
          in
          let expected:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G1.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              expected
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  c_k
                  x_pow
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
          in
          let x_pow:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Ops.Arith.f_mul_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              x_pow
              x
          in
          expected, x_pow
          <:
          (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
  in
  let actual:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config =
    Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
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
      share
  in
  expected =. actual

/// Compute the expected public key share for a given index from the VSS commitment.
/// Per Round 1 line 8 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "X_{j,k} = product_{l=0}^{t-1} A_{j,l}^{k^l}"
/// Returns `g^{f(index)} = product_{k=0}^{t-1} C_k^{index^k}`, which is the
/// commitment to the share value at `index` without revealing the share itself.
let expected_share_commitment
      (commitment:
          t_Slice
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (index: u32)
    : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
  let x:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (cast (index <: u32) <: u64)
  in
  let result:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let x_pow:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 1)
  in
  let
  (result: Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
  (x_pow:
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
          #FStar.Tactics.Typeclasses.solve
          commitment
        <:
        Core_models.Slice.Iter.t_Iter
        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config))
      (result, x_pow
        <:
        (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (fun temp_0_ c_k ->
          let
          (result:
            Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config),
          (x_pow:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
            temp_0_
          in
          let c_k:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config
          =
            c_k
          in
          let result:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G1.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G1.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              result
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G1.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  c_k
                  x_pow
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config
              )
          in
          let x_pow:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Ops.Arith.f_mul_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              x_pow
              x
          in
          result, x_pow
          <:
          (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
  in
  Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
      Ark_bls12_381_.Curves.G1.t_Config)
    #FStar.Tactics.Typeclasses.solve
    result
