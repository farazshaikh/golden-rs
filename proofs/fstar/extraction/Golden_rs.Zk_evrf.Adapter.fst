module Golden_rs.Zk_evrf.Adapter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ff.Biginteger in
  let open Ark_ff.Fields in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_ff.Fields.Prime in
  let open Ark_relations.R1cs.Constraint_system in
  let open Ark_relations.R1cs.Error in
  let open Libspartan.Errors in
  ()

/// Result of synthesizing a circuit: the R1CS matrices and witness assignment.
/// Contains everything needed to produce an IPA proof: the constraint matrices
/// (for future full R1CS reduction) and the complete variable assignment
/// (used as the IPA `a`-vector in the current prototype).
type t_CapturedR1CS = {
  f_num_inputs:usize;
  f_num_witness:usize;
  f_num_constraints:usize;
  f_matrices:Ark_relations.R1cs.Constraint_system.t_ConstraintMatrices
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4));
  f_assignment:Alloc.Vec.t_Vec
    (Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
}

/// Synthesize a circuit and capture all R1CS data.
/// Creates an arkworks constraint system in proving mode, runs the circuit
/// synthesizer, checks satisfaction, and extracts the matrices and assignment.
/// Returns an error if synthesis fails or the circuit is unsatisfied.
let capture_circuit
      (#v_C: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Ark_relations.R1cs.Constraint_system.t_ConstraintSynthesizer v_C
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      (circuit: v_C)
    : Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String =
  let cs:Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4)) =
    Ark_relations.R1cs.Constraint_system.impl_1__new_ref #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      ()
  in
  let _:Prims.unit =
    Ark_relations.R1cs.Constraint_system.impl_7__set_mode #(Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
      cs
      (Ark_relations.R1cs.Constraint_system.SynthesisMode_Prove
        ({ Ark_relations.R1cs.Constraint_system.f_construct_matrices = true })
        <:
        Ark_relations.R1cs.Constraint_system.t_SynthesisMode)
  in
  match
    Core_models.Result.impl__map_err #Prims.unit
      #Ark_relations.R1cs.Error.t_SynthesisError
      #Alloc.String.t_String
      #(Ark_relations.R1cs.Error.t_SynthesisError -> Alloc.String.t_String)
      (Ark_relations.R1cs.Constraint_system.f_generate_constraints #v_C
          #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          #FStar.Tactics.Typeclasses.solve
          circuit
          (Core_models.Clone.f_clone #(Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #FStar.Tactics.Typeclasses.solve
              cs
            <:
            Ark_relations.R1cs.Constraint_system.t_ConstraintSystemRef
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Core_models.Result.t_Result Prims.unit Ark_relations.R1cs.Error.t_SynthesisError)
      (fun e ->
          let e:Ark_relations.R1cs.Error.t_SynthesisError = e in
          let args:Ark_relations.R1cs.Error.t_SynthesisError =
            e <: Ark_relations.R1cs.Error.t_SynthesisError
          in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
            let list =
              [Core_models.Fmt.Rt.impl__new_display #Ark_relations.R1cs.Error.t_SynthesisError args]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          Core_models.Hint.must_use #Alloc.String.t_String
            (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                    (mk_usize 1)
                    (let list = ["Circuit synthesis failed: "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    args
                  <:
                  Core_models.Fmt.t_Arguments)
              <:
              Alloc.String.t_String))
    <:
    Core_models.Result.t_Result Prims.unit Alloc.String.t_String
  with
  | Core_models.Result.Result_Ok _ ->
    let _:Prims.unit =
      Ark_relations.R1cs.Constraint_system.impl_7__finalize #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        cs
    in
    (match
        Core_models.Result.impl__map_err #bool
          #Ark_relations.R1cs.Error.t_SynthesisError
          #Alloc.String.t_String
          #(Ark_relations.R1cs.Error.t_SynthesisError -> Alloc.String.t_String)
          (Ark_relations.R1cs.Constraint_system.impl_7__is_satisfied #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              cs
            <:
            Core_models.Result.t_Result bool Ark_relations.R1cs.Error.t_SynthesisError)
          (fun e ->
              let e:Ark_relations.R1cs.Error.t_SynthesisError = e in
              let args:Ark_relations.R1cs.Error.t_SynthesisError =
                e <: Ark_relations.R1cs.Error.t_SynthesisError
              in
              let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                let list =
                  [
                    Core_models.Fmt.Rt.impl__new_display #Ark_relations.R1cs.Error.t_SynthesisError
                      args
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list
              in
              Core_models.Hint.must_use #Alloc.String.t_String
                (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                        (mk_usize 1)
                        (let list = ["Satisfaction check failed: "] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                        args
                      <:
                      Core_models.Fmt.t_Arguments)
                  <:
                  Alloc.String.t_String))
        <:
        Core_models.Result.t_Result bool Alloc.String.t_String
      with
      | Core_models.Result.Result_Ok is_satisfied ->
        if ~.is_satisfied
        then
          Core_models.Result.Result_Err
          (Alloc.String.f_to_string #string
              #FStar.Tactics.Typeclasses.solve
              "Circuit is not satisfied by the provided witness")
          <:
          Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String
        else
          let num_inputs:usize =
            (Ark_relations.R1cs.Constraint_system.impl_7__num_instance_variables #(Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                cs
              <:
              usize) -!
            mk_usize 1
          in
          let num_witness:usize =
            Ark_relations.R1cs.Constraint_system.impl_7__num_witness_variables #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              cs
          in
          let num_constraints:usize =
            Ark_relations.R1cs.Constraint_system.impl_7__num_constraints #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              cs
          in
          (match
              Core_models.Option.impl__ok_or #(Ark_relations.R1cs.Constraint_system.t_ConstraintMatrices
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                #string
                (Ark_relations.R1cs.Constraint_system.impl_7__to_matrices #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    cs
                  <:
                  Core_models.Option.t_Option
                  (Ark_relations.R1cs.Constraint_system.t_ConstraintMatrices
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
                "Failed to extract constraint matrices"
              <:
              Core_models.Result.t_Result
                (Ark_relations.R1cs.Constraint_system.t_ConstraintMatrices
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))) string
            with
            | Core_models.Result.Result_Ok matrices ->
              (match
                  Core_models.Option.impl__ok_or #(Core_models.Cell.t_Ref
                      (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
                    #string
                    (Ark_relations.R1cs.Constraint_system.impl_7__borrow #(Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        cs
                      <:
                      Core_models.Option.t_Option
                      (Core_models.Cell.t_Ref
                        (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                          (Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))))
                    "Failed to borrow constraint system"
                  <:
                  Core_models.Result.t_Result
                    (Core_models.Cell.t_Ref
                      (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))))
                    string
                with
                | Core_models.Result.Result_Ok inner ->
                  let a:Alloc.Vec.t_Vec
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global =
                    Alloc.Vec.impl__with_capacity #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      ((Alloc.Vec.impl_1__len #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #Alloc.Alloc.t_Global
                            (Core_models.Ops.Deref.f_deref #(Core_models.Cell.t_Ref
                                  (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))))
                                #FStar.Tactics.Typeclasses.solve
                                inner
                              <:
                              Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              ))
                              .Ark_relations.R1cs.Constraint_system.f_instance_assignment
                          <:
                          usize) +!
                        (Alloc.Vec.impl_1__len #(Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                            #Alloc.Alloc.t_Global
                            (Core_models.Ops.Deref.f_deref #(Core_models.Cell.t_Ref
                                  (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                                    (Ark_ff.Fields.Models.Fp.t_Fp
                                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                        (mk_usize 4))))
                                #FStar.Tactics.Typeclasses.solve
                                inner
                              <:
                              Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                              (Ark_ff.Fields.Models.Fp.t_Fp
                                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
                              ))
                              .Ark_relations.R1cs.Constraint_system.f_witness_assignment
                          <:
                          usize)
                        <:
                        usize)
                  in
                  let a:Alloc.Vec.t_Vec
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_2__extend_from_slice #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #Alloc.Alloc.t_Global
                      a
                      (Alloc.Vec.impl_1__as_slice (Core_models.Ops.Deref.f_deref #(Core_models.Cell.t_Ref
                                (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))))
                              #FStar.Tactics.Typeclasses.solve
                              inner
                            <:
                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                            .Ark_relations.R1cs.Constraint_system.f_instance_assignment
                        <:
                        t_Slice
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  in
                  let a:Alloc.Vec.t_Vec
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global =
                    Alloc.Vec.impl_2__extend_from_slice #(Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      #Alloc.Alloc.t_Global
                      a
                      (Alloc.Vec.impl_1__as_slice (Core_models.Ops.Deref.f_deref #(Core_models.Cell.t_Ref
                                (Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                                  (Ark_ff.Fields.Models.Fp.t_Fp
                                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4))
                                      (mk_usize 4))))
                              #FStar.Tactics.Typeclasses.solve
                              inner
                            <:
                            Ark_relations.R1cs.Constraint_system.t_ConstraintSystem
                            (Ark_ff.Fields.Models.Fp.t_Fp
                                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                            .Ark_relations.R1cs.Constraint_system.f_witness_assignment
                        <:
                        t_Slice
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  in
                  let assignment:Alloc.Vec.t_Vec
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    Alloc.Alloc.t_Global =
                    a
                  in
                  Core_models.Result.Result_Ok
                  ({
                      f_num_inputs = num_inputs;
                      f_num_witness = num_witness;
                      f_num_constraints = num_constraints;
                      f_matrices = matrices;
                      f_assignment = assignment
                    }
                    <:
                    t_CapturedR1CS)
                  <:
                  Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String
                | Core_models.Result.Result_Err err ->
                  Core_models.Result.Result_Err
                  (Core_models.Convert.f_from #Alloc.String.t_String
                      #string
                      #FStar.Tactics.Typeclasses.solve
                      err)
                  <:
                  Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String)
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err
              (Core_models.Convert.f_from #Alloc.String.t_String
                  #string
                  #FStar.Tactics.Typeclasses.solve
                  err)
              <:
              Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_CapturedR1CS Alloc.String.t_String

/// Conversion result: ark-spartan Instance + assignments extracted from a captured circuit.
type t_SpartanData = {
  f_instance:Libspartan.t_Instance
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4));
  f_vars:Libspartan.t_Assignment
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4));
  f_inputs:Libspartan.t_Assignment
  (Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4));
  f_num_cons:usize;
  f_num_vars:usize;
  f_num_inputs:usize
}

/// Convert a captured arkworks R1CS circuit to ark-spartan format.
/// Performs the column index remapping between arkworks ordering
/// (z = [1, public_inputs, witnesses]) and ark-spartan ordering
/// (z = [vars, 1, inputs]).
let to_spartan (captured: t_CapturedR1CS)
    : Core_models.Result.t_Result t_SpartanData Alloc.String.t_String =
  let num_instance_vars:usize = captured.f_num_inputs +! mk_usize 1 in
  let num_witness:usize = captured.f_num_witness in
  let num_cons:usize = captured.f_num_constraints in
  let num_inputs:usize = captured.f_num_inputs in
  let convert_matrix:
      t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global)
    -> Alloc.Vec.t_Vec
        (usize & usize &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
  =
    fun ark_matrix ->
      let ark_matrix:t_Slice
      (Alloc.Vec.t_Vec
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
            usize) Alloc.Alloc.t_Global) =
        ark_matrix
      in
      let triples:Alloc.Vec.t_Vec
        (usize & usize &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
      =
        Alloc.Vec.impl__new #(usize & usize &
            Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          ()
      in
      let triples:Alloc.Vec.t_Vec
        (usize & usize &
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
      =
        Rust_primitives.Hax.Folds.fold_enumerated_slice ark_matrix
          (fun triples temp_1_ ->
              let triples:Alloc.Vec.t_Vec
                (usize & usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                Alloc.Alloc.t_Global =
                triples
              in
              let _:usize = temp_1_ in
              true)
          triples
          (fun triples temp_1_ ->
              let triples:Alloc.Vec.t_Vec
                (usize & usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                Alloc.Alloc.t_Global =
                triples
              in
              let
              (row: usize),
              (row_entries:
                Alloc.Vec.t_Vec
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    usize) Alloc.Alloc.t_Global) =
                temp_1_
              in
              Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(
                      Alloc.Vec.t_Vec
                        (Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                          usize) Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    row_entries
                  <:
                  Core_models.Slice.Iter.t_Iter
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    usize))
                triples
                (fun triples temp_1_ ->
                    let triples:Alloc.Vec.t_Vec
                      (usize & usize &
                        Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      Alloc.Alloc.t_Global =
                      triples
                    in
                    let
                    (coeff:
                      Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)),
                    (ark_col: usize) =
                      temp_1_
                    in
                    let spartan_col:usize =
                      if ark_col =. mk_usize 0
                      then num_witness
                      else
                        if ark_col <. num_instance_vars
                        then num_witness +! ark_col
                        else ark_col -! num_instance_vars
                    in
                    let triples:Alloc.Vec.t_Vec
                      (usize & usize &
                        Ark_ff.Fields.Models.Fp.t_Fp
                          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                      Alloc.Alloc.t_Global =
                      Alloc.Vec.impl_1__push #(usize & usize &
                          Ark_ff.Fields.Models.Fp.t_Fp
                            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                        #Alloc.Alloc.t_Global
                        triples
                        (row, spartan_col, coeff
                          <:
                          (usize & usize &
                            Ark_ff.Fields.Models.Fp.t_Fp
                              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                    in
                    triples)
              <:
              Alloc.Vec.t_Vec
                (usize & usize &
                  Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                Alloc.Alloc.t_Global)
      in
      triples
  in
  let a_triples:Alloc.Vec.t_Vec
    (usize & usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Core_models.Ops.Function.f_call #(
            t_Slice
              (Alloc.Vec.t_Vec
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    usize) Alloc.Alloc.t_Global)
          -> Alloc.Vec.t_Vec
              (usize & usize &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global)
      #(t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
      #FStar.Tactics.Typeclasses.solve
      convert_matrix
      ((Alloc.Vec.impl_1__as_slice captured.f_matrices.Ark_relations.R1cs.Constraint_system.f_a
          <:
          t_Slice
          (Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                usize) Alloc.Alloc.t_Global))
        <:
        t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
  in
  let b_triples:Alloc.Vec.t_Vec
    (usize & usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Core_models.Ops.Function.f_call #(
            t_Slice
              (Alloc.Vec.t_Vec
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    usize) Alloc.Alloc.t_Global)
          -> Alloc.Vec.t_Vec
              (usize & usize &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global)
      #(t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
      #FStar.Tactics.Typeclasses.solve
      convert_matrix
      ((Alloc.Vec.impl_1__as_slice captured.f_matrices.Ark_relations.R1cs.Constraint_system.f_b
          <:
          t_Slice
          (Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                usize) Alloc.Alloc.t_Global))
        <:
        t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
  in
  let c_triples:Alloc.Vec.t_Vec
    (usize & usize &
      Ark_ff.Fields.Models.Fp.t_Fp
        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
    Core_models.Ops.Function.f_call #(
            t_Slice
              (Alloc.Vec.t_Vec
                  (Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                    usize) Alloc.Alloc.t_Global)
          -> Alloc.Vec.t_Vec
              (usize & usize &
                Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              Alloc.Alloc.t_Global)
      #(t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
      #FStar.Tactics.Typeclasses.solve
      convert_matrix
      ((Alloc.Vec.impl_1__as_slice captured.f_matrices.Ark_relations.R1cs.Constraint_system.f_c
          <:
          t_Slice
          (Alloc.Vec.t_Vec
              (Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
                usize) Alloc.Alloc.t_Global))
        <:
        t_Slice
        (Alloc.Vec.t_Vec
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) &
              usize) Alloc.Alloc.t_Global))
  in
  match
    Core_models.Result.impl__map_err #(Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      #Libspartan.Errors.t_R1CSError
      #Alloc.String.t_String
      #(Libspartan.Errors.t_R1CSError -> Alloc.String.t_String)
      (Libspartan.impl_1__new #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          num_cons
          num_witness
          num_inputs
          (Alloc.Vec.impl_1__as_slice a_triples
            <:
            t_Slice
            (usize & usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (Alloc.Vec.impl_1__as_slice b_triples
            <:
            t_Slice
            (usize & usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          (Alloc.Vec.impl_1__as_slice c_triples
            <:
            t_Slice
            (usize & usize &
              Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
        <:
        Core_models.Result.t_Result
          (Libspartan.t_Instance
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          Libspartan.Errors.t_R1CSError)
      (fun e ->
          let e:Libspartan.Errors.t_R1CSError = e in
          let args:Libspartan.Errors.t_R1CSError = e <: Libspartan.Errors.t_R1CSError in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
            let list = [Core_models.Fmt.Rt.impl__new_debug #Libspartan.Errors.t_R1CSError args] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          Core_models.Hint.must_use #Alloc.String.t_String
            (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                    (mk_usize 1)
                    (let list = ["Failed to create Spartan instance: "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    args
                  <:
                  Core_models.Fmt.t_Arguments)
              <:
              Alloc.String.t_String))
    <:
    Core_models.Result.t_Result
      (Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
      Alloc.String.t_String
  with
  | Core_models.Result.Result_Ok v_instance ->
    let
    (input_values:
      Alloc.Vec.t_Vec
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
    ):Alloc.Vec.t_Vec
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
      Alloc.Slice.impl__to_vec #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        (captured.f_assignment.[ {
              Core_models.Ops.Range.f_start = mk_usize 1;
              Core_models.Ops.Range.f_end = num_instance_vars
            }
            <:
            Core_models.Ops.Range.t_Range usize ]
          <:
          t_Slice
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    in
    let
    (witness_values:
      Alloc.Vec.t_Vec
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global
    ):Alloc.Vec.t_Vec
      (Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) Alloc.Alloc.t_Global =
      Alloc.Slice.impl__to_vec #(Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        (captured.f_assignment.[ { Core_models.Ops.Range.f_start = num_instance_vars }
            <:
            Core_models.Ops.Range.t_RangeFrom usize ]
          <:
          t_Slice
          (Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
    in
    (match
        Core_models.Result.impl__map_err #(Libspartan.t_Assignment
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          #Libspartan.Errors.t_R1CSError
          #Alloc.String.t_String
          #(Libspartan.Errors.t_R1CSError -> Alloc.String.t_String)
          (Libspartan.impl__new #(Ark_ff.Fields.Models.Fp.t_Fp
                  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
              (Alloc.Vec.impl_1__as_slice witness_values
                <:
                t_Slice
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
            <:
            Core_models.Result.t_Result
              (Libspartan.t_Assignment
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              Libspartan.Errors.t_R1CSError)
          (fun e ->
              let e:Libspartan.Errors.t_R1CSError = e in
              let args:Libspartan.Errors.t_R1CSError = e <: Libspartan.Errors.t_R1CSError in
              let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                let list =
                  [Core_models.Fmt.Rt.impl__new_debug #Libspartan.Errors.t_R1CSError args]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list
              in
              Core_models.Hint.must_use #Alloc.String.t_String
                (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                        (mk_usize 1)
                        (let list = ["Failed to create VarsAssignment: "] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                        args
                      <:
                      Core_models.Fmt.t_Arguments)
                  <:
                  Alloc.String.t_String))
        <:
        Core_models.Result.t_Result
          (Libspartan.t_Assignment
            (Ark_ff.Fields.Models.Fp.t_Fp
                (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
          Alloc.String.t_String
      with
      | Core_models.Result.Result_Ok vars ->
        (match
            Core_models.Result.impl__map_err #(Libspartan.t_Assignment
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              #Libspartan.Errors.t_R1CSError
              #Alloc.String.t_String
              #(Libspartan.Errors.t_R1CSError -> Alloc.String.t_String)
              (Libspartan.impl__new #(Ark_ff.Fields.Models.Fp.t_Fp
                      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                          Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                  (Alloc.Vec.impl_1__as_slice input_values
                    <:
                    t_Slice
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                <:
                Core_models.Result.t_Result
                  (Libspartan.t_Assignment
                    (Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
                  Libspartan.Errors.t_R1CSError)
              (fun e ->
                  let e:Libspartan.Errors.t_R1CSError = e in
                  let args:Libspartan.Errors.t_R1CSError = e <: Libspartan.Errors.t_R1CSError in
                  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
                    let list =
                      [Core_models.Fmt.Rt.impl__new_debug #Libspartan.Errors.t_R1CSError args]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list
                  in
                  Core_models.Hint.must_use #Alloc.String.t_String
                    (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                            (mk_usize 1)
                            (let list = ["Failed to create InputsAssignment: "] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list)
                            args
                          <:
                          Core_models.Fmt.t_Arguments)
                      <:
                      Alloc.String.t_String))
            <:
            Core_models.Result.t_Result
              (Libspartan.t_Assignment
                (Ark_ff.Fields.Models.Fp.t_Fp
                    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                        Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)))
              Alloc.String.t_String
          with
          | Core_models.Result.Result_Ok inputs ->
            Core_models.Result.Result_Ok
            ({
                f_instance = v_instance;
                f_vars = vars;
                f_inputs = inputs;
                f_num_cons = num_cons;
                f_num_vars = num_witness;
                f_num_inputs = num_inputs
              }
              <:
              t_SpartanData)
            <:
            Core_models.Result.t_Result t_SpartanData Alloc.String.t_String
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result t_SpartanData Alloc.String.t_String)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result t_SpartanData Alloc.String.t_String)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result t_SpartanData Alloc.String.t_String

/// Convert an arkworks R1CS to a Spartan Instance without assignments.
/// Used by the verifier, which only needs the constraint structure + public inputs.
let to_spartan_instance_only (captured: t_CapturedR1CS)
    : Core_models.Result.t_Result
      (Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) &
        usize &
        usize &
        usize) Alloc.String.t_String =
  match to_spartan captured <: Core_models.Result.t_Result t_SpartanData Alloc.String.t_String with
  | Core_models.Result.Result_Ok data ->
    Core_models.Result.Result_Ok
    (data.f_instance, data.f_num_cons, data.f_num_vars, data.f_num_inputs
      <:
      (Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) &
        usize &
        usize &
        usize))
    <:
    Core_models.Result.t_Result
      (Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) &
        usize &
        usize &
        usize) Alloc.String.t_String
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result
      (Libspartan.t_Instance
        (Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)) &
        usize &
        usize &
        usize) Alloc.String.t_String
