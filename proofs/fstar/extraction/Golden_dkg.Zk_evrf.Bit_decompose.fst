module Golden_dkg.Zk_evrf.Bit_decompose
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
let bit_decompose
      (cs: Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem)
      (value:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (lambda: usize)
    : (Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem & t_BitDecomposition) =
  let value_bits:Alloc.Vec.t_Vec bool Alloc.Alloc.t_Global =
    Ark_ff.Biginteger.f_to_bits_le #(Ark_ff.Biginteger.t_BigInt (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      (Ark_ff.Fields.Prime.f_into_bigint #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          value
        <:
        Ark_ff.Biginteger.t_BigInt (mk_usize 4))
  in
  let (tmp0: Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem), (out: usize) =
    Golden_dkg.Zk_evrf.Nonnative.impl_ConstraintSystem__alloc_witness cs value
  in
  let cs:Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem = tmp0 in
  let value_var:usize = out in
  let bits:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity #usize (lambda +! mk_usize 1 <: usize)
  in
  let
  (bits: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global),
  (cs: Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem) =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Core_models.Ops.Range.t_RangeInclusive
            usize)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Range.impl_7__new #usize (mk_usize 0) lambda
            <:
            Core_models.Ops.Range.t_RangeInclusive usize)
        <:
        Core_models.Ops.Range.t_RangeInclusive usize)
      (bits, cs
        <:
        (Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global &
          Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem))
      (fun temp_0_ i ->
          let
          (bits: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global),
          (cs: Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem) =
            temp_0_
          in
          let i:usize = i in
          let bit_val:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            if
              i <. (Alloc.Vec.impl_1__len #bool #Alloc.Alloc.t_Global value_bits <: usize) &&
              value_bits.[ i ]
            then
              Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #FStar.Tactics.Typeclasses.solve
                ()
            else
              Num_traits.Identities.f_zero #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #FStar.Tactics.Typeclasses.solve
                ()
          in
          let (tmp0: Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem), (out: usize) =
            Golden_dkg.Zk_evrf.Nonnative.impl_ConstraintSystem__alloc_witness cs bit_val
          in
          let cs:Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem = tmp0 in
          let bit_var:usize = out in
          let cs:Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem =
            Golden_dkg.Zk_evrf.Nonnative.impl_ConstraintSystem__constrain cs
              (Alloc.Slice.impl__into_vec #(usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #Alloc.Alloc.t_Global
                  ((let list =
                        [
                          bit_var,
                          Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #FStar.Tactics.Typeclasses.solve
                            ()
                          <:
                          (usize &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice
                    (usize &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                <:
                Alloc.Vec.t_Vec
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global)
              (Alloc.Slice.impl__into_vec #(usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #Alloc.Alloc.t_Global
                  ((let list =
                        [
                          bit_var,
                          Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #FStar.Tactics.Typeclasses.solve
                            ()
                          <:
                          (usize &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice
                    (usize &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                <:
                Alloc.Vec.t_Vec
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global)
              (Alloc.Slice.impl__into_vec #(usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #Alloc.Alloc.t_Global
                  ((let list =
                        [
                          bit_var,
                          Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #FStar.Tactics.Typeclasses.solve
                            ()
                          <:
                          (usize &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice
                    (usize &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                <:
                Alloc.Vec.t_Vec
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global)
          in
          let bits:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #usize #Alloc.Alloc.t_Global bits bit_var
          in
          bits, cs
          <:
          (Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global &
            Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem))
  in
  let power_of_two:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let recomp_terms:Alloc.Vec.t_Vec
    (usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(usize &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      ()
  in
  let recomp_terms:Alloc.Vec.t_Vec
    (usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              usize Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          bits
        <:
        Core_models.Slice.Iter.t_Iter usize)
      recomp_terms
      (fun recomp_terms bit_var ->
          let recomp_terms:Alloc.Vec.t_Vec
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global =
            recomp_terms
          in
          let bit_var:usize = bit_var in
          let recomp_terms:Alloc.Vec.t_Vec
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #(usize &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #Alloc.Alloc.t_Global
              recomp_terms
              (bit_var, power_of_two
                <:
                (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          in
          recomp_terms)
  in
  let cs:Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem =
    Golden_dkg.Zk_evrf.Nonnative.impl_ConstraintSystem__constrain cs
      recomp_terms
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  mk_usize 0,
                  Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #FStar.Tactics.Typeclasses.solve
                    ()
                  <:
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Alloc.Vec.t_Vec
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          Alloc.Alloc.t_Global)
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  value_var,
                  Num_traits.Identities.f_one #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #FStar.Tactics.Typeclasses.solve
                    ()
                  <:
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Alloc.Vec.t_Vec
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          Alloc.Alloc.t_Global)
  in
  let hax_temp_output:t_BitDecomposition =
    { f_bits = bits; f_value_var = value_var } <: t_BitDecomposition
  in
  cs, hax_temp_output <: (Golden_dkg.Zk_evrf.Nonnative.t_ConstraintSystem & t_BitDecomposition)

/// Count the number of constraints for a bit decomposition.
/// Per Section 4.4: `lambda + 1` (bit constraints) + 1 (recomposition) = `lambda + 2`.
let constraint_count (lambda: usize) : usize = lambda +! mk_usize 2
