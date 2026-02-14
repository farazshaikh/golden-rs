module Golden_rs.Shamir
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_std.Rand_helper in
  let open Rand.Distributions.Distribution in
  let open Rand.Rng in
  ()

/// A polynomial over the scalar field, used for Shamir secret sharing.
/// Per Section 3.3 of the Golden paper (IACR 2025/1924), Share(x, n, t):
/// > "Define polynomial f(Z) = x + a_1*Z + ... + a_{t-1}*Z^{t-1} with random
/// > a_1,...,a_{t-1}"
/// `coefficients[0]` is the secret (constant term `a_0`), and subsequent
/// coefficients are the random blinding terms.
type t_Polynomial = {
  f_coefficients:Alloc.Vec.t_Vec
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
}

/// Create a random polynomial of the given degree whose constant term is `secret`.
/// Per Section 3.3 of the Golden paper (IACR 2025/1924):
/// > "Define polynomial f(Z) = x + a_1*Z + ... + a_{t-1}*Z^{t-1} with random
/// > a_1,...,a_{t-1}"
/// For threshold `t`, use `degree = t - 1`. The constant term is fixed to
/// `secret`, and the remaining `degree` coefficients are sampled uniformly
/// at random from Z_p.
let impl_Polynomial__new_random
      (#iimpl_1039969868_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand.Rng.t_Rng iimpl_1039969868_)
      (secret:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (degree: usize)
      (rng: iimpl_1039969868_)
    : (iimpl_1039969868_ & t_Polynomial) =
  let coefficients:Alloc.Vec.t_Vec
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (degree +! mk_usize 1 <: usize)
  in
  let coefficients:Alloc.Vec.t_Vec
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Alloc.Vec.impl_1__push #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #Alloc.Alloc.t_Global
      coefficients
      secret
  in
  let
  (coefficients:
    Alloc.Vec.t_Vec
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global),
  (rng: iimpl_1039969868_) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      degree
      (fun temp_0_ temp_1_ ->
          let
          (coefficients:
            Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global),
          (rng: iimpl_1039969868_) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (coefficients, rng
        <:
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global &
          iimpl_1039969868_))
      (fun temp_0_ temp_1_ ->
          let
          (coefficients:
            Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global),
          (rng: iimpl_1039969868_) =
            temp_0_
          in
          let _:usize = temp_1_ in
          let
          (tmp0: iimpl_1039969868_),
          (out:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
            Ark_std.Rand_helper.f_rand #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              #iimpl_1039969868_
              rng
          in
          let rng:iimpl_1039969868_ = tmp0 in
          Alloc.Vec.impl_1__push #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #Alloc.Alloc.t_Global
            coefficients
            out,
          rng
          <:
          (Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global &
            iimpl_1039969868_))
  in
  let hax_temp_output:t_Polynomial = { f_coefficients = coefficients } <: t_Polynomial in
  rng, hax_temp_output <: (iimpl_1039969868_ & t_Polynomial)

/// Evaluate the polynomial at `x` using Horner's method.
/// Computes `f(x) = a_0 + x*(a_1 + x*(a_2 + ... + x*a_n))` by walking
/// coefficients from highest degree down to the constant term. This is
/// numerically stable and requires only `degree` multiplications.
/// NOTE: Uses index-based access instead of `iter().rev()` for hax
/// extraction compatibility. Iterator adapters (Rev, Map) generate
/// dependent closure types in F* that fail typeclass resolution.
/// Index-based loops extract as simple `fold_range` with no closures.
/// See: formal_verification/Implementation.md "Extraction-Friendly Rust"
let impl_Polynomial__evaluate
      (self: t_Polynomial)
      (x:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  let result:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 0)
  in
  let n:usize =
    Alloc.Vec.impl_1__len #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #Alloc.Alloc.t_Global
      self.f_coefficients
  in
  let result:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      n
      (fun result temp_1_ ->
          let result:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result idx ->
          let result:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            result
          in
          let idx:usize = idx in
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
                result
                x
              <:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            (self.f_coefficients.[ (n -! mk_usize 1 <: usize) -! idx <: usize ]
              <:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          <:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  in
  result

/// Return the degree of the polynomial.
let impl_Polynomial__degree (self: t_Polynomial) : usize =
  (Alloc.Vec.impl_1__len #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #Alloc.Alloc.t_Global
      self.f_coefficients
    <:
    usize) -!
  mk_usize 1

/// Generate `n` shares by evaluating the polynomial at x = 1, 2, ..., n.
/// Per Section 3.3 of the Golden paper (IACR 2025/1924):
/// > "Each share x_bar_i = f(i) for i in [n]"
/// Returns `(node_id, share_value)` pairs with `node_id` in `1..=n`.
/// The evaluation points are the natural numbers 1 through n, which ensures
/// they are distinct and nonzero (as required for Lagrange interpolation).
/// NOTE: Uses explicit push loop instead of `map().collect()` for hax
/// extraction compatibility. See: formal_verification/Implementation.md
/// "Extraction-Friendly Rust"
let generate_shares (poly: t_Polynomial) (n: u32)
    : Alloc.Vec.t_Vec
      (u32 &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
  let shares:Alloc.Vec.t_Vec
    (u32 &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity #(u32 &
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      (cast (n <: u32) <: usize)
  in
  let shares:Alloc.Vec.t_Vec
    (u32 &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_u32 0)
      n
      (fun shares temp_1_ ->
          let shares:Alloc.Vec.t_Vec
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global =
            shares
          in
          let _:u32 = temp_1_ in
          true)
      shares
      (fun shares idx ->
          let shares:Alloc.Vec.t_Vec
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global =
            shares
          in
          let idx:u32 = idx in
          let i:u32 = idx +! mk_u32 1 in
          let x:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #u64
              #FStar.Tactics.Typeclasses.solve
              (cast (i <: u32) <: u64)
          in
          let shares:Alloc.Vec.t_Vec
            (u32 &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #(u32 &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #Alloc.Alloc.t_Global
              shares
              (i,
                (impl_Polynomial__evaluate poly x
                  <:
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                <:
                (u32 &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          in
          shares)
  in
  shares

/// Reconstruct `f(0)` (the secret) from a set of shares using Lagrange interpolation.
/// Per Section 3.3 of the Golden paper (IACR 2025/1924), Recover(t, {(i, x_bar_i)}):
/// > "x = sum_{i in C} x_bar_i * L_i(0)
/// > where L_i(0) = product_{j in C, j != i} j / (j - i)"
/// Each share is `(node_id, y_i)` where `x_i = Scalar::from(node_id)`.
/// Requires at least `t` shares for a degree-`(t-1)` polynomial.
let lagrange_interpolate_at_zero
      (shares:
          t_Slice
          (u32 &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  let result:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #u64
      #FStar.Tactics.Typeclasses.solve
      (mk_u64 0)
  in
  Rust_primitives.Hax.Folds.fold_enumerated_slice shares
    (fun result temp_1_ ->
        let result:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          result
        in
        let _:usize = temp_1_ in
        true)
    result
    (fun result temp_1_ ->
        let result:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          result
        in
        let
        (i: usize),
        ((xi_id: u32),
          (yi:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
          temp_1_
        in
        let xi:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #u64
            #FStar.Tactics.Typeclasses.solve
            (cast (xi_id <: u32) <: u64)
        in
        let li:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            #u64
            #FStar.Tactics.Typeclasses.solve
            (mk_u64 1)
        in
        let li:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          Rust_primitives.Hax.Folds.fold_enumerated_slice shares
            (fun li temp_1_ ->
                let li:Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                  li
                in
                let _:usize = temp_1_ in
                true)
            li
            (fun li temp_1_ ->
                let li:Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
                  li
                in
                let
                (j: usize),
                ((xj_id: u32),
                  (_:
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) =
                  temp_1_
                in
                if i =. j <: bool
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
                      (cast (xj_id <: u32) <: u64)
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
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
                                #FStar.Tactics.Typeclasses.solve
                                (Core_models.Ops.Arith.f_sub #(Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                    #(Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))
                                    #FStar.Tactics.Typeclasses.solve
                                    xj
                                    xi
                                  <:
                                  Ark_ff.Fields.Models.Fp.t_Fp
                                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                    (mk_usize 4))
                              <:
                              Core_models.Option.t_Option
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              ))
                            "duplicate x values in shares"
                          <:
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      <:
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        in
        Core_models.Ops.Arith.f_add_assign #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          result
          (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              yi
              li
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
