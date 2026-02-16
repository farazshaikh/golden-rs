module Golden_dkg.Threshold.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves in
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Curves.G2 in
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fq12 in
  let open Ark_bls12_381_.Fields.Fq2 in
  let open Ark_bls12_381_.Fields.Fq6 in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec in
  let open Ark_ec.Models.Bls12 in
  let open Ark_ec.Models.Bls12.G1 in
  let open Ark_ec.Models.Bls12.G2 in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ec.Models.Short_weierstrass.Group in
  let open Ark_ec.Pairing in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Models.Cubic_extension in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Models.Fp12_2over3over2 in
  let open Ark_ff.Fields.Models.Fp2 in
  let open Ark_ff.Fields.Models.Fp6_3over2 in
  let open Ark_ff.Fields.Models.Quadratic_extension in
  let open Std.Collections.Hash.Map in
  let open Std.Hash.Random in
  ()

/// Precomputed Lagrange coefficients for each selected subset.
/// After construction, each entry in `subsets` contains the `(node_id, coeff)`
/// pairs for one threshold-sized subset. The first subset is always used for
/// combination; additional subsets are used for cross-checking.
type t_LagrangeCache = {
  f_subsets:Alloc.Vec.t_Vec
    (Alloc.Vec.t_Vec
        (u32 &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
    ) Alloc.Alloc.t_Global
}

/// Compute a partial BLS signature: `sigma_i = H(m)^{sk_i}`.
/// The caller must hash the message to a G2 point first (see
/// [`crate::beacon::hash_to_g2`]).
let partial_sign
      (msg_hash: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      (share: Golden_dkg.Threshold.Types.t_KeyShare)
    : Golden_dkg.Threshold.Types.t_PartialSignature =
  let sig:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G2.t_Config)
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          msg_hash
          share.Golden_dkg.Threshold.Types.f_secret
        <:
        Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config)
  in
  {
    Golden_dkg.Threshold.Types.f_signer = share.Golden_dkg.Threshold.Types.f_id;
    Golden_dkg.Threshold.Types.f_signature = sig
  }
  <:
  Golden_dkg.Threshold.Types.t_PartialSignature

/// Verify a single partial signature against the signer's public key share.
/// Checks `e(pk_i, H(m)) == e(g1, sigma_i)` via a pairing comparison.
let verify_partial
      (msg_hash: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      (partial: Golden_dkg.Threshold.Types.t_PartialSignature)
      (pk_share: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : bool =
  let g1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      pk_share
      msg_hash
    <:
    Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)) =.
  (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      g1
      partial.Golden_dkg.Threshold.Types.f_signature
    <:
    Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))

/// Verify a threshold signature against the group public key.
/// Checks `e(PK, H(m)) == e(g1, sigma)` via a pairing comparison.
let verify
      (msg_hash: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      (sig: Golden_dkg.Threshold.Types.t_ThresholdSignature)
      (group_pk: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    : bool =
  let g1:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    Ark_ec.f_generator #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
        Ark_bls12_381_.Curves.G1.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      group_pk
      msg_hash
    <:
    Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)) =.
  (Ark_ec.Pairing.f_pairing #(Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config)
      #FStar.Tactics.Typeclasses.solve
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
      #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      g1
      sig.Golden_dkg.Threshold.Types.f_signature
    <:
    Ark_ec.Pairing.t_PairingOutput (Ark_ec.Models.Bls12.t_Bls12 Ark_bls12_381_.Curves.t_Config))

/// Compute the Lagrange coefficient for `node_id` given the set of signer IDs.
/// Returns `l_i(0) = prod_{j != i} (x_j / (x_j - x_i))` where evaluation
/// points are the node IDs cast to field elements.
let lagrange_coeff (node_id: u32) (all_ids: t_Slice u32)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  let xi:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (cast (node_id <: u32) <: u64)
  in
  let li:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 1)
  in
  Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice u32
        )
        #FStar.Tactics.Typeclasses.solve
        all_ids
      <:
      Core_models.Slice.Iter.t_Iter u32)
    li
    (fun li id ->
        let li:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          li
        in
        let id:u32 = id in
        if id =. node_id <: bool
        then li
        else
          let xj:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #u64
              #FStar.Tactics.Typeclasses.solve
              (cast (id <: u32) <: u64)
          in
          Core_models.Ops.Arith.f_mul_assign #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #FStar.Tactics.Typeclasses.solve
            li
            (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #FStar.Tactics.Typeclasses.solve
                xj
                (Core_models.Option.impl__expect #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    (Ark_ff.Fields.f_inverse #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #FStar.Tactics.Typeclasses.solve
                            xj
                            xi
                          <:
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      <:
                      Core_models.Option.t_Option
                      (Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    "duplicate node IDs"
                  <:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              <:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))

/// Combine a single subset of partial signatures using precomputed Lagrange coefficients.
/// This is the inner workhorse used by [`combine`] and the multi-subset checker.
let combine_one
      (subset_coeffs:
          t_Slice
          (u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (partials:
          Std.Collections.Hash.Map.t_HashMap u32
            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
            Std.Hash.Random.t_RandomState)
    : Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
  let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
  =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
  =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #FStar.Tactics.Typeclasses.solve
          subset_coeffs
        <:
        Core_models.Slice.Iter.t_Iter
        (u32 &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      combined
      (fun combined temp_1_ ->
          let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            combined
          in
          let
          (id: u32),
          (li:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
            temp_1_
          in
          let sig_i:Ark_ec.Models.Short_weierstrass.Affine.t_Affine
          Ark_bls12_381_.Curves.G2.t_Config =
            partials.[ id ]
          in
          let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              combined
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G2.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  sig_i
                  li
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
          in
          combined)
  in
  Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
      Ark_bls12_381_.Curves.G2.t_Config)
    #FStar.Tactics.Typeclasses.solve
    combined

/// Combine `>= threshold` partial signatures into a threshold signature.
/// Uses precomputed Lagrange coefficients from the cache. Only the first
/// subset in the cache is used for combination (use
/// [`combine_and_check`] to cross-check multiple subsets).
/// # Panics
/// Panics if the cache has no subsets or if a required partial is missing.
let combine
      (partials: t_Slice Golden_dkg.Threshold.Types.t_PartialSignature)
      (e_signer_ids: t_Slice u32)
      (cache: t_LagrangeCache)
    : Golden_dkg.Threshold.Types.t_ThresholdSignature =
  let
  (partial_map:
    Std.Collections.Hash.Map.t_HashMap u32
      (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
      Std.Hash.Random.t_RandomState):Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
    Std.Hash.Random.t_RandomState =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (Golden_dkg.Threshold.Types.t_PartialSignature
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          ))
      #FStar.Tactics.Typeclasses.solve
      #(Std.Collections.Hash.Map.t_HashMap u32
          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          Std.Hash.Random.t_RandomState)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
            Golden_dkg.Threshold.Types.t_PartialSignature)
          #FStar.Tactics.Typeclasses.solve
          #(u32 & Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          #(Golden_dkg.Threshold.Types.t_PartialSignature
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          )
          (Core_models.Slice.impl__iter #Golden_dkg.Threshold.Types.t_PartialSignature partials
            <:
            Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (fun p ->
              let p:Golden_dkg.Threshold.Types.t_PartialSignature = p in
              p.Golden_dkg.Threshold.Types.f_signer, p.Golden_dkg.Threshold.Types.f_signature
              <:
              (u32 &
                Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (Golden_dkg.Threshold.Types.t_PartialSignature
              -> (u32 &
                  Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config)
          ))
  in
  let combined:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config =
    combine_one (Alloc.Vec.impl_1__as_slice (cache.f_subsets.[ mk_usize 0 ]
            <:
            Alloc.Vec.t_Vec
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global)
        <:
        t_Slice
        (u32 &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      partial_map
  in
  { Golden_dkg.Threshold.Types.f_signature = combined }
  <:
  Golden_dkg.Threshold.Types.t_ThresholdSignature

/// Combine partial signatures by computing Lagrange coefficients on the fly.
/// Unlike [`combine`], this does not require a precomputed cache. It takes the
/// first `threshold` partials, computes their Lagrange coefficients, and
/// interpolates. Useful when the signer set is dynamic (e.g., Byzantine
/// double-voting creates non-standard signer subsets).
let combine_dynamic
      (partials: t_Slice Golden_dkg.Threshold.Types.t_PartialSignature)
      (threshold: usize)
    : Golden_dkg.Threshold.Types.t_ThresholdSignature =
  let partials:t_Slice Golden_dkg.Threshold.Types.t_PartialSignature =
    if
      (Core_models.Slice.impl__len #Golden_dkg.Threshold.Types.t_PartialSignature partials <: usize) >.
      threshold
    then
      partials.[ { Core_models.Ops.Range.f_end = threshold }
        <:
        Core_models.Ops.Range.t_RangeTo usize ]
    else partials
  in
  let (signer_ids: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u32
    Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (Golden_dkg.Threshold.Types.t_PartialSignature -> u32))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
            Golden_dkg.Threshold.Types.t_PartialSignature)
          #FStar.Tactics.Typeclasses.solve
          #u32
          #(Golden_dkg.Threshold.Types.t_PartialSignature -> u32)
          (Core_models.Slice.impl__iter #Golden_dkg.Threshold.Types.t_PartialSignature partials
            <:
            Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (fun p ->
              let p:Golden_dkg.Threshold.Types.t_PartialSignature = p in
              p.Golden_dkg.Threshold.Types.f_signer)
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
          (Golden_dkg.Threshold.Types.t_PartialSignature -> u32))
  in
  let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
  =
    Core_models.Default.f_default #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
  =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            Golden_dkg.Threshold.Types.t_PartialSignature)
          #FStar.Tactics.Typeclasses.solve
          partials
        <:
        Core_models.Slice.Iter.t_Iter Golden_dkg.Threshold.Types.t_PartialSignature)
      combined
      (fun combined p ->
          let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            combined
          in
          let p:Golden_dkg.Threshold.Types.t_PartialSignature = p in
          let li:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            lagrange_coeff p.Golden_dkg.Threshold.Types.f_signer
              (Alloc.Vec.impl_1__as_slice signer_ids <: t_Slice u32)
          in
          let combined:Ark_ec.Models.Short_weierstrass.Group.t_Projective
          Ark_bls12_381_.Curves.G2.t_Config =
            Core_models.Ops.Arith.f_add_assign #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
                Ark_bls12_381_.Curves.G2.t_Config)
              #(Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
              #FStar.Tactics.Typeclasses.solve
              combined
              (Core_models.Ops.Arith.f_mul #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                    Ark_bls12_381_.Curves.G2.t_Config)
                  #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  #FStar.Tactics.Typeclasses.solve
                  p.Golden_dkg.Threshold.Types.f_signature
                  li
                <:
                Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G2.t_Config
              )
          in
          combined)
  in
  {
    Golden_dkg.Threshold.Types.f_signature
    =
    Ark_ec.f_into_affine #(Ark_ec.Models.Short_weierstrass.Group.t_Projective
        Ark_bls12_381_.Curves.G2.t_Config)
      #FStar.Tactics.Typeclasses.solve
      combined
  }
  <:
  Golden_dkg.Threshold.Types.t_ThresholdSignature

/// Enumerate all `k`-element combinations of `items`.
/// Returns a `Vec` of sorted sub-slices. Used to enumerate all possible
/// threshold-signing subsets for cross-checking.
let rec combinations (items: t_Slice u32) (k: usize)
    : Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global =
  if k =. mk_usize 0
  then
    Alloc.Slice.impl__into_vec #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
      #Alloc.Alloc.t_Global
      ((let list = [Alloc.Vec.impl__new #u32 ()] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global))
  else
    if (Core_models.Slice.impl__len #u32 items <: usize) <. k
    then Alloc.Vec.impl__new #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) ()
    else
      let result:Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global =
        Alloc.Vec.impl__new #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) ()
      in
      let first:u32 = items.[ mk_usize 0 ] in
      let rest:t_Slice u32 =
        items.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
      in
      let
      (combo: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global),
      (result: Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global) =
        Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
                  (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              (combinations rest (k -! mk_usize 1 <: usize)
                <:
                Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
            <:
            Alloc.Vec.Into_iter.t_IntoIter (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
              Alloc.Alloc.t_Global)
          (combo, result
            <:
            (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global &
              Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global))
          (fun temp_0_ combo ->
              let
              (combo: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global),
              (result:
                Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global) =
                temp_0_
              in
              let combo:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = combo in
              let combo:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
                Alloc.Vec.impl_1__insert #u32 #Alloc.Alloc.t_Global combo (mk_usize 0) first
              in
              let result:Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
                Alloc.Alloc.t_Global =
                Alloc.Vec.impl_1__push #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
                  #Alloc.Alloc.t_Global
                  result
                  combo
              in
              combo, result
              <:
              (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global &
                Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global))
      in
      Core_models.Iter.Traits.Collect.f_extend #(Alloc.Vec.t_Vec
            (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
        #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        #(Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
        result
        (combinations rest k
          <:
          Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)

/// Build a cache by selecting `num_check` evenly-spaced subsets from all
/// `C(n, t)` combinations of `node_ids`.
/// If `num_check` is 1, only the first subset is stored (fast path).
/// If `num_check >= C(n,t)`, all subsets are stored.
let impl__new (node_ids: t_Slice u32) (t: u32) (num_check: usize) : t_LagrangeCache =
  let all_subsets:Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global =
    combinations node_ids (cast (t <: u32) <: usize)
  in
  let v_total:usize =
    Alloc.Vec.impl_1__len #(Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
      #Alloc.Alloc.t_Global
      all_subsets
  in
  let (indices: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global):Alloc.Vec.t_Vec usize
    Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #usize ()
  in
  let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
    if v_total <=. num_check || num_check <=. mk_usize 1
    then
      let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
        Core_models.Iter.Traits.Collect.f_extend #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
          #usize
          #FStar.Tactics.Typeclasses.solve
          #(Core_models.Ops.Range.t_Range usize)
          indices
          ({
              Core_models.Ops.Range.f_start = mk_usize 0;
              Core_models.Ops.Range.f_end
              =
              Core_models.Cmp.f_min #usize
                #FStar.Tactics.Typeclasses.solve
                v_total
                (Core_models.Cmp.f_max #usize
                    #FStar.Tactics.Typeclasses.solve
                    num_check
                    (mk_usize 1)
                  <:
                  usize)
              <:
              usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
      in
      indices
    else
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        num_check
        (fun indices temp_1_ ->
            let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global = indices in
            let _:usize = temp_1_ in
            true)
        indices
        (fun indices i ->
            let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global = indices in
            let i:usize = i in
            Alloc.Vec.impl_1__push #usize
              #Alloc.Alloc.t_Global
              indices
              ((i *! (v_total -! mk_usize 1 <: usize) <: usize) /!
                (num_check -! mk_usize 1 <: usize)
                <:
                usize)
            <:
            Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
  in
  let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec (Alloc.Slice.impl__sort #usize
          (Alloc.Vec.impl_1__as_slice indices <: t_Slice usize)
        <:
        t_Slice usize)
  in
  let indices:Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global =
    Alloc.Vec.impl_5__dedup #usize #Alloc.Alloc.t_Global indices
  in
  let subsets:Alloc.Vec.t_Vec
    (Alloc.Vec.t_Vec
        (u32 &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
    ) Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Alloc.Vec.Into_iter.t_IntoIter usize Alloc.Alloc.t_Global)
          (usize
              -> Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec
          (Alloc.Vec.t_Vec
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Alloc.Vec.Into_iter.t_IntoIter usize
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          #(Alloc.Vec.t_Vec
              (u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global)
          #(usize
              -> Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global)
          (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              indices
            <:
            Alloc.Vec.Into_iter.t_IntoIter usize Alloc.Alloc.t_Global)
          (fun idx ->
              let idx:usize = idx in
              let subset:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = all_subsets.[ idx ] in
              Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                    (Core_models.Slice.Iter.t_Iter u32)
                    (u32
                        -> (u32 &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
                #FStar.Tactics.Typeclasses.solve
                #(Alloc.Vec.t_Vec
                    (u32 &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global)
                (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter u32)
                    #FStar.Tactics.Typeclasses.solve
                    #(u32 &
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #(u32
                        -> (u32 &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    (Core_models.Slice.impl__iter #u32
                        (Alloc.Vec.impl_1__as_slice subset <: t_Slice u32)
                      <:
                      Core_models.Slice.Iter.t_Iter u32)
                    (fun id ->
                        let id:u32 = id in
                        id,
                        (lagrange_coeff id (Alloc.Vec.impl_1__as_slice subset <: t_Slice u32)
                          <:
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        <:
                        (u32 &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  <:
                  Core_models.Iter.Adapters.Map.t_Map (Core_models.Slice.Iter.t_Iter u32)
                    (u32
                        -> (u32 &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))))
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Alloc.Vec.Into_iter.t_IntoIter usize Alloc.Alloc.t_Global)
          (usize
              -> Alloc.Vec.t_Vec
                  (u32 &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  Alloc.Alloc.t_Global))
  in
  { f_subsets = subsets } <: t_LagrangeCache
