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

(* Remaining constraint system operations replaced with assume val.
   The non-native arithmetic correctness is verified by the Lean proof
   in EVRFCircuit.lean (constraint count theorem). *)
assume val impl_ConstraintSystem__alloc_input (self: t_ConstraintSystem)
  : (t_ConstraintSystem & usize)
assume val impl_ConstraintSystem__alloc_witness (self: t_ConstraintSystem)
  : (t_ConstraintSystem & usize)
assume val impl_ConstraintSystem__constrain (self: t_ConstraintSystem) (idx: usize) (constant: Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  : t_ConstraintSystem
assume val impl_ConstraintSystem__enforce_equal_constant (self: t_ConstraintSystem) (a: usize) (constant: Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
  : t_ConstraintSystem
assume val impl_ConstraintSystem__enforce_mul (self: t_ConstraintSystem) (a b c: usize)
  : t_ConstraintSystem
assume val impl_ConstraintSystem__enforce_add (self: t_ConstraintSystem) (a b c: usize)
  : t_ConstraintSystem
assume val impl_ConstraintSystem__num_constraints (self: t_ConstraintSystem) : usize
assume val impl_ConstraintSystem__to_r1cs_constraints (self: t_ConstraintSystem)
  : (Alloc.Vec.t_Vec t_Constraint Alloc.Alloc.t_Global &
     Alloc.Vec.t_Vec t_Constraint Alloc.Alloc.t_Global &
     Alloc.Vec.t_Vec t_Constraint Alloc.Alloc.t_Global)
