module Golden_rs.Zk_evrf.Nonnative
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Fields.Fq in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  ()

/// A single R1CS constraint: `<a, z> * <b, z> = <c, z>`
/// Stored as sparse vectors of `(variable_index, coefficient)`.
type t_Constraint = {
  f_a:Alloc.Vec.t_Vec
    (usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global;
  f_b:Alloc.Vec.t_Vec
    (usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global;
  f_c:Alloc.Vec.t_Vec
    (usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
}

let impl_2: Core_models.Clone.t_Clone t_Constraint =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_Constraint

unfold
let impl_3 = impl_3'

/// Constraint system that accumulates R1CS constraints.
/// Variables are indexed starting from 0 (constant 1), then public inputs,
/// then witnesses. The system supports both constraint generation (for circuit
/// definition) and satisfaction checking (for testing).
type t_ConstraintSystem = {
  f_num_vars:usize;
  f_num_inputs:usize;
  f_constraints:Alloc.Vec.t_Vec t_Constraint Alloc.Alloc.t_Global;
  f_witness:Alloc.Vec.t_Vec
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
}

/// Create a new constraint system. Variable 0 is the constant 1.
let impl_ConstraintSystem__new (_: Prims.unit) : t_ConstraintSystem =
  {
    f_num_vars = mk_usize 1;
    f_num_inputs = mk_usize 0;
    f_constraints = Alloc.Vec.impl__new #t_Constraint ();
    f_witness
    =
    Alloc.Slice.impl__into_vec #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #Alloc.Alloc.t_Global
      ((let list =
            [
              Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #u64
                #FStar.Tactics.Typeclasses.solve
                (mk_u64 1)
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
  }
  <:
  t_ConstraintSystem

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Default.t_Default t_ConstraintSystem =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_ConstraintSystem) -> true);
    f_default = fun (_: Prims.unit) -> impl_ConstraintSystem__new ()
  }

/// Allocate a new public input variable and set its witness value.
let impl_ConstraintSystem__alloc_input
      (self: t_ConstraintSystem)
      (value:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : (t_ConstraintSystem & usize) =
  let idx:usize = self.f_num_vars in
  let self:t_ConstraintSystem =
    { self with f_num_vars = self.f_num_vars +! mk_usize 1 } <: t_ConstraintSystem
  in
  let self:t_ConstraintSystem =
    { self with f_num_inputs = self.f_num_inputs +! mk_usize 1 } <: t_ConstraintSystem
  in
  let self:t_ConstraintSystem =
    {
      self with
      f_witness
      =
      Alloc.Vec.impl_1__push #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        #Alloc.Alloc.t_Global
        self.f_witness
        value
    }
    <:
    t_ConstraintSystem
  in
  let hax_temp_output:usize = idx in
  self, hax_temp_output <: (t_ConstraintSystem & usize)

/// Allocate a new private witness variable and set its value.
let impl_ConstraintSystem__alloc_witness
      (self: t_ConstraintSystem)
      (value:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : (t_ConstraintSystem & usize) =
  let idx:usize = self.f_num_vars in
  let self:t_ConstraintSystem =
    { self with f_num_vars = self.f_num_vars +! mk_usize 1 } <: t_ConstraintSystem
  in
  let self:t_ConstraintSystem =
    {
      self with
      f_witness
      =
      Alloc.Vec.impl_1__push #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        #Alloc.Alloc.t_Global
        self.f_witness
        value
    }
    <:
    t_ConstraintSystem
  in
  let hax_temp_output:usize = idx in
  self, hax_temp_output <: (t_ConstraintSystem & usize)

/// Add a constraint: `<a, z> * <b, z> = <c, z>`.
let impl_ConstraintSystem__constrain
      (self: t_ConstraintSystem)
      (a b c:
          Alloc.Vec.t_Vec
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global)
    : t_ConstraintSystem =
  let self:t_ConstraintSystem =
    {
      self with
      f_constraints
      =
      Alloc.Vec.impl_1__push #t_Constraint
        #Alloc.Alloc.t_Global
        self.f_constraints
        ({ f_a = a; f_b = b; f_c = c } <: t_Constraint)
    }
    <:
    t_ConstraintSystem
  in
  self

/// Enforce that variable `var` equals a known constant value.
/// Constraint: `var * 1 = constant`.
let impl_ConstraintSystem__enforce_equal_constant
      (self: t_ConstraintSystem)
      (var: usize)
      (constant:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_ConstraintSystem =
  let self:t_ConstraintSystem =
    impl_ConstraintSystem__constrain self
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  var,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  mk_usize 0,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  mk_usize 0, constant
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
  self

/// Enforce multiplication: `a * b = c` (all are variable indices).
let impl_ConstraintSystem__enforce_mul (self: t_ConstraintSystem) (a b c: usize)
    : t_ConstraintSystem =
  let self:t_ConstraintSystem =
    impl_ConstraintSystem__constrain self
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  a,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  b,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  c,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
  self

/// Enforce addition: `a + b = c`.
/// Implemented as: `(a + b) * 1 = c`.
let impl_ConstraintSystem__enforce_add (self: t_ConstraintSystem) (a b c: usize)
    : t_ConstraintSystem =
  let self:t_ConstraintSystem =
    impl_ConstraintSystem__constrain self
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  a,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
                  <:
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4));
                  b,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
                  <:
                  (usize &
                    Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
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
                  mk_usize 0,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  c,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
  self

/// Enforce linear combination: `sum(coeff_i * var_i) = result`.
let impl_ConstraintSystem__enforce_lc_equals
      (self: t_ConstraintSystem)
      (terms:
          Alloc.Vec.t_Vec
            (usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            Alloc.Alloc.t_Global)
      (result: usize)
    : t_ConstraintSystem =
  let self:t_ConstraintSystem =
    impl_ConstraintSystem__constrain self
      terms
      (Alloc.Slice.impl__into_vec #(usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #Alloc.Alloc.t_Global
          ((let list =
                [
                  mk_usize 0,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
                  result,
                  Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    #u64
                    #FStar.Tactics.Typeclasses.solve
                    (mk_u64 1)
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
  self

/// Allocate a witness variable for `a * b` and enforce the multiplication constraint.
/// Returns the index of the product variable.
let impl_ConstraintSystem__mul (self: t_ConstraintSystem) (a b: usize)
    : (t_ConstraintSystem & usize) =
  let a_val:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    self.f_witness.[ a ]
  in
  let b_val:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    self.f_witness.[ b ]
  in
  let c_val:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4) =
    Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      #FStar.Tactics.Typeclasses.solve
      a_val
      b_val
  in
  let (tmp0: t_ConstraintSystem), (out: usize) = impl_ConstraintSystem__alloc_witness self c_val in
  let self:t_ConstraintSystem = tmp0 in
  let c:usize = out in
  let self:t_ConstraintSystem = impl_ConstraintSystem__enforce_mul self a b c in
  let hax_temp_output:usize = c in
  self, hax_temp_output <: (t_ConstraintSystem & usize)

/// Return the number of constraints.
let impl_ConstraintSystem__num_constraints (self: t_ConstraintSystem) : usize =
  Alloc.Vec.impl_1__len #t_Constraint #Alloc.Alloc.t_Global self.f_constraints

/// Evaluate a linear combination given witness values.
let eval_lc
      (lc:
          t_Slice
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (witness:
          t_Slice
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  Core_models.Iter.Traits.Iterator.f_fold #(Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Slice.Iter.t_Iter
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (
              (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            -> Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    #FStar.Tactics.Typeclasses.solve
    #(Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    #(
          Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) ->
          Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
        -> Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        #FStar.Tactics.Typeclasses.solve
        #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        #(
              (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            -> Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        (Core_models.Slice.impl__iter #(usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            lc
          <:
          Core_models.Slice.Iter.t_Iter
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (fun temp_0_ ->
            let
            (idx: usize),
            (coeff:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) =
              temp_0_
            in
            Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              #FStar.Tactics.Typeclasses.solve
              (witness.[ idx ]
                <:
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              coeff
            <:
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      <:
      Core_models.Iter.Adapters.Map.t_Map
        (Core_models.Slice.Iter.t_Iter
          (usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        (
              (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
            -> Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    (Core_models.Convert.f_from #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        #u64
        #FStar.Tactics.Typeclasses.solve
        (mk_u64 0)
      <:
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    (fun a b ->
        let a:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          a
        in
        let b:Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
          b
        in
        Core_models.Ops.Arith.f_add #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          a
          b
        <:
        Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))

/// Check if all constraints are satisfied by the current witness.
let impl_ConstraintSystem__is_satisfied (self: t_ConstraintSystem) : bool =
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              t_Constraint Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          self.f_constraints
        <:
        Core_models.Slice.Iter.t_Iter t_Constraint)
      ()
      (fun temp_0_ constraint ->
          let _:Prims.unit = temp_0_ in
          let constraint:t_Constraint = constraint in
          let a_val:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            eval_lc (Alloc.Vec.impl_1__as_slice constraint.f_a
                <:
                t_Slice
                (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              (Alloc.Vec.impl_1__as_slice self.f_witness
                <:
                t_Slice
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          in
          let b_val:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            eval_lc (Alloc.Vec.impl_1__as_slice constraint.f_b
                <:
                t_Slice
                (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              (Alloc.Vec.impl_1__as_slice self.f_witness
                <:
                t_Slice
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          in
          let c_val:Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) =
            eval_lc (Alloc.Vec.impl_1__as_slice constraint.f_c
                <:
                t_Slice
                (usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              (Alloc.Vec.impl_1__as_slice self.f_witness
                <:
                t_Slice
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          in
          if
            (Core_models.Ops.Arith.f_mul #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                #FStar.Tactics.Typeclasses.solve
                a_val
                b_val
              <:
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) <>.
            c_val
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break false
              <:
              Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> true

/// Convert an Fq element to Fr (reduce mod r).
/// Per Appendix E of the Golden paper (IACR 2025/1924), when the eVRF operates
/// on a single curve (`G_in = G_out`), point coordinates in Fq must be represented
/// as Fr witness variables. This conversion is lossy for large Fq values (> Fr modulus)
/// but the circuit compensates with sufficient constraints to uniquely determine
/// the correct values.
let fq_to_fr
      (v_val:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) =
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Ark_ff.Biginteger.f_to_bytes_le #(Ark_ff.Biginteger.t_BigInt (mk_usize 6))
      #FStar.Tactics.Typeclasses.solve
      (Ark_ff.Fields.Prime.f_into_bigint #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6))
          #FStar.Tactics.Typeclasses.solve
          v_val
        <:
        Ark_ff.Biginteger.t_BigInt (mk_usize 6))
  in
  Ark_ff.Fields.Prime.f_from_le_bytes_mod_order #(Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    #FStar.Tactics.Typeclasses.solve
    (Alloc.Vec.impl_1__as_slice bytes <: t_Slice u8)
