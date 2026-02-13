module Golden_rs.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ark_bls12_381_.Curves.G1 in
  let open Ark_bls12_381_.Fields.Fr in
  let open Ark_ec.Models.Short_weierstrass in
  let open Ark_ec.Models.Short_weierstrass.Affine in
  let open Ark_ff.Fields.Models.Fp in
  let open Ark_ff.Fields.Models.Fp.Montgomery_backend in
  let open Ark_serialize in
  let open Ark_serialize.Error in
  let open Borsh.De in
  let open Borsh.Ser in
  let open Golden_rs.Zk_evrf in
  let open Std.Collections.Hash.Map in
  let open Std.Hash.Random in
  let open Std.Io in
  let open Std.Io.Impls in
  ()

/// A scalar value that is zeroed from memory on drop.
/// SECURITY: Wraps `Fr` (BLS12-381 scalar field) for secret keys,
/// polynomial coefficients, and other sensitive values. The internal
/// representation is overwritten with zeros when the value goes out of scope.
type t_SecretScalar =
  | SecretScalar :
      Ark_ff.Fields.Models.Fp.t_Fp
          (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
              Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)
    -> t_SecretScalar

/// Create a new secret scalar.
let impl_SecretScalar__new
      (v_val:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
    : t_SecretScalar = SecretScalar v_val <: t_SecretScalar

/// Get the inner scalar value.
let impl_SecretScalar__inner (self: t_SecretScalar)
    : Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4) = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Ops.Deref.t_Deref t_SecretScalar =
  {
    f_Target
    =
    Ark_ff.Fields.Models.Fp.t_Fp
      (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
          (mk_usize 4)) (mk_usize 4);
    f_deref_pre = (fun (self: t_SecretScalar) -> true);
    f_deref_post
    =
    (fun
        (self: t_SecretScalar)
        (out:
          Ark_ff.Fields.Models.Fp.t_Fp
            (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
        ->
        true);
    f_deref = fun (self: t_SecretScalar) -> self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Ops.Drop.t_Drop t_SecretScalar =
  {
    f_drop_pre = (fun (self: t_SecretScalar) -> true);
    f_drop_post = (fun (self: t_SecretScalar) (out: t_SecretScalar) -> true);
    f_drop
    =
    fun (self: t_SecretScalar) ->
      let _:Prims.unit =
        Rust_primitives.Hax.failure "Explicit rejection by a phase in the Hax engine:\na node of kind [Raw_pointer] have been found in the AST\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n"
          "{\n let ptr: raw_pointer!() = { cast(address_of) };\n {\n let len: int = {\n core_models::mem::size_of::<\n ark_ff::fields::models::fp::t_Fp<\n ark_ff::fields::models::fp::montgomery_backend::t_MontBackend<..."

      in
      self
  }

/// Helper: serialize an arkworks type to bytes via CanonicalSerialize (compressed).
let ark_to_bytes
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Ark_serialize.t_CanonicalSerialize v_T)
      (v_val: v_T)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let buf:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let _:Prims.unit =
    Core_models.Result.impl__expect #Prims.unit
      #Ark_serialize.Error.t_SerializationError
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "ark_serialize::f_serialize_compressed::<\n &mut alloc::vec::t_Vec<int, alloc::alloc::t_Global>,\n >(&(deref(val)), &mut (buf))"

        <:
        Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError)
      "ark serialization failed"
  in
  buf

/// Helper: deserialize an arkworks type from bytes via CanonicalDeserialize (compressed).
let ark_from_bytes
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Ark_serialize.t_CanonicalDeserialize v_T)
      (bytes: t_Slice u8)
    : v_T =
  Core_models.Result.impl__expect #v_T
    #Ark_serialize.Error.t_SerializationError
    (Ark_serialize.f_deserialize_compressed #v_T
        #FStar.Tactics.Typeclasses.solve
        #(t_Slice u8)
        bytes
      <:
      Core_models.Result.t_Result v_T Ark_serialize.Error.t_SerializationError)
    "ark deserialization failed"

/// A single encrypted share from node i to node j.
/// Per Round 0 line 7 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "sigma_{i,j} = (R_{i,j}, z_{i,j})"
/// where `R_{i,j} = g^{r_{i,j}}` is the eVRF pad commitment and
/// `z_{i,j} = r_{i,j} + x_bar_{i,j}` is the encrypted Shamir share.
type t_Ciphertext = {
  f_r_commitment:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_encrypted_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl_7: Core_models.Clone.t_Clone t_Ciphertext =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Fmt.t_Debug t_Ciphertext

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Borsh.Ser.t_BorshSerialize t_Ciphertext =
  {
    f_serialize_pre
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
        (self: t_Ciphertext)
        (writer: v_W)
        ->
        true);
    f_serialize_post
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
        (self: t_Ciphertext)
        (writer: v_W)
        (out1: (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
        ->
        true);
    f_serialize
    =
    fun
      (#v_W: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
      (self: t_Ciphertext)
      (writer: v_W)
      ->
      let r_bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        ark_to_bytes #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
            Ark_bls12_381_.Curves.G1.t_Config)
          self.f_r_commitment
      in
      let s_bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        ark_to_bytes #(Ark_ff.Fields.Models.Fp.t_Fp
              (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                  Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
          self.f_encrypted_share
      in
      let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
        Borsh.Ser.f_serialize #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          #v_W
          r_bytes
          writer
      in
      let writer:v_W = tmp0 in
      match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
      | Core_models.Result.Result_Ok _ ->
        let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
          Borsh.Ser.f_serialize #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            #v_W
            s_bytes
            writer
        in
        let writer:v_W = tmp0 in
        (match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
          | Core_models.Result.Result_Ok _ ->
            let hax_temp_output:Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error =
              Core_models.Result.Result_Ok (() <: Prims.unit)
              <:
              Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error
            in
            writer, hax_temp_output
            <:
            (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
          | Core_models.Result.Result_Err err ->
            writer,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
            <:
            (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
      | Core_models.Result.Result_Err err ->
        writer,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        <:
        (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Borsh.De.t_BorshDeserialize t_Ciphertext =
  {
    f_deserialize_reader_pre
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
        (reader: v_R)
        ->
        true);
    f_deserialize_reader_post
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
        (reader: v_R)
        (out1: (v_R & Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error))
        ->
        true);
    f_deserialize_reader
    =
    fun
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
      (reader: v_R)
      ->
      let
      (tmp0: v_R),
      (out:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Std.Io.Error.t_Error)
      =
        Borsh.De.f_deserialize_reader #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          #v_R
          reader
      in
      let reader:v_R = tmp0 in
      match
        out
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Std.Io.Error.t_Error
      with
      | Core_models.Result.Result_Ok (r_bytes: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
        let
        (tmp0: v_R),
        (out:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Std.Io.Error.t_Error
        ) =
          Borsh.De.f_deserialize_reader #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            #v_R
            reader
        in
        let reader:v_R = tmp0 in
        (match
            out
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              Std.Io.Error.t_Error
          with
          | Core_models.Result.Result_Ok (s_bytes: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
            let hax_temp_output:Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error =
              Core_models.Result.Result_Ok
              ({
                  f_r_commitment
                  =
                  ark_from_bytes #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                      Ark_bls12_381_.Curves.G1.t_Config)
                    (Alloc.Vec.impl_1__as_slice r_bytes <: t_Slice u8);
                  f_encrypted_share
                  =
                  ark_from_bytes #(Ark_ff.Fields.Models.Fp.t_Fp
                        (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
                            Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4))
                    (Alloc.Vec.impl_1__as_slice s_bytes <: t_Slice u8)
                }
                <:
                t_Ciphertext)
              <:
              Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error
            in
            reader, hax_temp_output
            <:
            (v_R & Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error)
          | Core_models.Result.Result_Err err ->
            reader,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error)
            <:
            (v_R & Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error))
      | Core_models.Result.Result_Err err ->
        reader,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error)
        <:
        (v_R & Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error)
  }

/// Round 0 broadcast message from a single node.
/// Per Round 0 lines 9-10 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "bmsg_i = {(msg_i, C_bar_i, sigma_{i,j}, pi_{i,j})} for j != i"
/// Contains the VSS commitment, encrypted shares for all peers, and eVRF proofs
/// demonstrating correct pad derivation.
type t_Round0Msg = {
  f_session_id:t_Array u8 (mk_usize 32);
  f_from:u32;
  f_random_msg:t_Array u8 (mk_usize 32);
  f_vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global;
  f_ciphertexts:Std.Collections.Hash.Map.t_HashMap u32 t_Ciphertext Std.Hash.Random.t_RandomState;
  f_evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
    Golden_rs.Zk_evrf.t_EVRFProof
    Std.Hash.Random.t_RandomState;
  f_batch_evrf_proof:Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof
}

let impl_9: Core_models.Clone.t_Clone t_Round0Msg =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Fmt.t_Debug t_Round0Msg

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Borsh.Ser.t_BorshSerialize t_Round0Msg =
  {
    f_serialize_pre
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
        (self: t_Round0Msg)
        (writer: v_W)
        ->
        true);
    f_serialize_post
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
        (self: t_Round0Msg)
        (writer: v_W)
        (out1: (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
        ->
        true);
    f_serialize
    =
    fun
      (#v_W: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W)
      (self: t_Round0Msg)
      (writer: v_W)
      ->
      let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
        Borsh.Ser.f_serialize #(t_Array u8 (mk_usize 32))
          #FStar.Tactics.Typeclasses.solve
          #v_W
          self.f_session_id
          writer
      in
      let writer:v_W = tmp0 in
      match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
      | Core_models.Result.Result_Ok _ ->
        let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
          Borsh.Ser.f_serialize #u32 #FStar.Tactics.Typeclasses.solve #v_W self.f_from writer
        in
        let writer:v_W = tmp0 in
        (match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
          | Core_models.Result.Result_Ok _ ->
            let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
              Borsh.Ser.f_serialize #(t_Array u8 (mk_usize 32))
                #FStar.Tactics.Typeclasses.solve
                #v_W
                self.f_random_msg
                writer
            in
            let writer:v_W = tmp0 in
            (match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
              | Core_models.Result.Result_Ok _ ->
                let
                (commitment_bytes:
                  Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                  (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global =
                  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                        (Core_models.Slice.Iter.t_Iter
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                        (
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config
                            -> Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                    #FStar.Tactics.Typeclasses.solve
                    #(Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global
                    )
                    (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                        #(
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config
                            -> Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                        (Core_models.Slice.impl__iter #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)
                            (Alloc.Vec.impl_1__as_slice self.f_vss_commitment
                              <:
                              t_Slice
                              (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config))
                          <:
                          Core_models.Slice.Iter.t_Iter
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                        ark_to_bytes
                      <:
                      Core_models.Iter.Adapters.Map.t_Map
                        (Core_models.Slice.Iter.t_Iter
                          (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                            Ark_bls12_381_.Curves.G1.t_Config))
                        (
                              Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config
                            -> Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                in
                let (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                =
                  Borsh.Ser.f_serialize #(Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    #v_W
                    commitment_bytes
                    writer
                in
                let writer:v_W = tmp0 in
                (match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
                  | Core_models.Result.Result_Ok _ ->
                    let (ct_entries: Alloc.Vec.t_Vec (u32 & t_Ciphertext) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                      (u32 & t_Ciphertext) Alloc.Alloc.t_Global =
                      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                            (Std.Collections.Hash.Map.t_Iter u32 t_Ciphertext)
                            ((u32 & t_Ciphertext) -> (u32 & t_Ciphertext)))
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec (u32 & t_Ciphertext) Alloc.Alloc.t_Global)
                        (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter
                                u32 t_Ciphertext)
                            #FStar.Tactics.Typeclasses.solve
                            #(u32 & t_Ciphertext)
                            #((u32 & t_Ciphertext) -> (u32 & t_Ciphertext))
                            (Std.Collections.Hash.Map.impl_1__iter #u32
                                #t_Ciphertext
                                #Std.Hash.Random.t_RandomState
                                self.f_ciphertexts
                              <:
                              Std.Collections.Hash.Map.t_Iter u32 t_Ciphertext)
                            (fun temp_0_ ->
                                let (k: u32), (v: t_Ciphertext) = temp_0_ in
                                k, v <: (u32 & t_Ciphertext))
                          <:
                          Core_models.Iter.Adapters.Map.t_Map
                            (Std.Collections.Hash.Map.t_Iter u32 t_Ciphertext)
                            ((u32 & t_Ciphertext) -> (u32 & t_Ciphertext)))
                    in
                    let len:u32 =
                      cast (Alloc.Vec.impl_1__len #(u32 & t_Ciphertext)
                            #Alloc.Alloc.t_Global
                            ct_entries
                          <:
                          usize)
                      <:
                      u32
                    in
                    let
                    (tmp0: v_W), (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                    =
                      Borsh.Ser.f_serialize #u32 #FStar.Tactics.Typeclasses.solve #v_W len writer
                    in
                    let writer:v_W = tmp0 in
                    (match out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error with
                      | Core_models.Result.Result_Ok _ ->
                        (match
                            Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                                  #(Alloc.Vec.t_Vec (u32 & t_Ciphertext) Alloc.Alloc.t_Global)
                                  #FStar.Tactics.Typeclasses.solve
                                  ct_entries
                                <:
                                Alloc.Vec.Into_iter.t_IntoIter (u32 & t_Ciphertext)
                                  Alloc.Alloc.t_Global)
                              writer
                              (fun writer temp_1_ ->
                                  let writer:v_W = writer in
                                  let (node_id: u32), (ct: t_Ciphertext) = temp_1_ in
                                  let
                                  (tmp0: v_W),
                                  (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                                  =
                                    Borsh.Ser.f_serialize #u32
                                      #FStar.Tactics.Typeclasses.solve
                                      #v_W
                                      node_id
                                      writer
                                  in
                                  let writer:v_W = tmp0 in
                                  match
                                    out
                                    <:
                                    Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error
                                  with
                                  | Core_models.Result.Result_Ok _ ->
                                    let
                                    (tmp0: v_W),
                                    (out:
                                      Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
                                      Borsh.Ser.f_serialize #t_Ciphertext
                                        #FStar.Tactics.Typeclasses.solve
                                        #v_W
                                        ct
                                        writer
                                    in
                                    let writer:v_W = tmp0 in
                                    (match
                                        out
                                        <:
                                        Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error
                                      with
                                      | Core_models.Result.Result_Ok _ ->
                                        Core_models.Ops.Control_flow.ControlFlow_Continue writer
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_W &
                                                Core_models.Result.t_Result Prims.unit
                                                  Std.Io.Error.t_Error) (Prims.unit & v_W)) v_W
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                          (writer,
                                            (Core_models.Result.Result_Err err
                                              <:
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error)
                                            <:
                                            (v_W &
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (v_W &
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error) (Prims.unit & v_W))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_W &
                                                Core_models.Result.t_Result Prims.unit
                                                  Std.Io.Error.t_Error) (Prims.unit & v_W)) v_W)
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                      (writer,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error)
                                        <:
                                        (v_W &
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (v_W &
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error) (Prims.unit & v_W))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (v_W &
                                            Core_models.Result.t_Result Prims.unit
                                              Std.Io.Error.t_Error) (Prims.unit & v_W)) v_W)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                              v_W
                          with
                          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                          | Core_models.Ops.Control_flow.ControlFlow_Continue writer ->
                            let
                            (proof_entries:
                              Alloc.Vec.t_Vec (u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                              (u32 & Golden_rs.Zk_evrf.t_EVRFProof) Alloc.Alloc.t_Global =
                              Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                                    (Std.Collections.Hash.Map.t_Iter u32
                                        Golden_rs.Zk_evrf.t_EVRFProof)
                                    ((u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                        -> (u32 & Golden_rs.Zk_evrf.t_EVRFProof)))
                                #FStar.Tactics.Typeclasses.solve
                                #(Alloc.Vec.t_Vec (u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                    Alloc.Alloc.t_Global)
                                (Core_models.Iter.Traits.Iterator.f_map #(Std.Collections.Hash.Map.t_Iter
                                        u32 Golden_rs.Zk_evrf.t_EVRFProof)
                                    #FStar.Tactics.Typeclasses.solve
                                    #(u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                    #((u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                        -> (u32 & Golden_rs.Zk_evrf.t_EVRFProof))
                                    (Std.Collections.Hash.Map.impl_1__iter #u32
                                        #Golden_rs.Zk_evrf.t_EVRFProof
                                        #Std.Hash.Random.t_RandomState
                                        self.f_evrf_proofs
                                      <:
                                      Std.Collections.Hash.Map.t_Iter u32
                                        Golden_rs.Zk_evrf.t_EVRFProof)
                                    (fun temp_0_ ->
                                        let (k: u32), (v: Golden_rs.Zk_evrf.t_EVRFProof) =
                                          temp_0_
                                        in
                                        k, v <: (u32 & Golden_rs.Zk_evrf.t_EVRFProof))
                                  <:
                                  Core_models.Iter.Adapters.Map.t_Map
                                    (Std.Collections.Hash.Map.t_Iter u32
                                        Golden_rs.Zk_evrf.t_EVRFProof)
                                    ((u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                        -> (u32 & Golden_rs.Zk_evrf.t_EVRFProof)))
                            in
                            let proof_len:u32 =
                              cast (Alloc.Vec.impl_1__len #(u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                    #Alloc.Alloc.t_Global
                                    proof_entries
                                  <:
                                  usize)
                              <:
                              u32
                            in
                            let
                            (tmp0: v_W),
                            (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
                              Borsh.Ser.f_serialize #u32
                                #FStar.Tactics.Typeclasses.solve
                                #v_W
                                proof_len
                                writer
                            in
                            let writer:v_W = tmp0 in
                            match
                              out <: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error
                            with
                            | Core_models.Result.Result_Ok _ ->
                              (match
                                  Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                                        #(Alloc.Vec.t_Vec (u32 & Golden_rs.Zk_evrf.t_EVRFProof)
                                            Alloc.Alloc.t_Global)
                                        #FStar.Tactics.Typeclasses.solve
                                        proof_entries
                                      <:
                                      Alloc.Vec.Into_iter.t_IntoIter
                                        (u32 & Golden_rs.Zk_evrf.t_EVRFProof) Alloc.Alloc.t_Global)
                                    writer
                                    (fun writer temp_1_ ->
                                        let writer:v_W = writer in
                                        let (node_id: u32), (proof: Golden_rs.Zk_evrf.t_EVRFProof) =
                                          temp_1_
                                        in
                                        let
                                        (tmp0: v_W),
                                        (out:
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error) =
                                          Borsh.Ser.f_serialize #u32
                                            #FStar.Tactics.Typeclasses.solve
                                            #v_W
                                            node_id
                                            writer
                                        in
                                        let writer:v_W = tmp0 in
                                        match
                                          out
                                          <:
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error
                                        with
                                        | Core_models.Result.Result_Ok _ ->
                                          let
                                          (tmp0: v_W),
                                          (out:
                                            Core_models.Result.t_Result Prims.unit
                                              Std.Io.Error.t_Error) =
                                            Borsh.Ser.f_serialize #Golden_rs.Zk_evrf.t_EVRFProof
                                              #FStar.Tactics.Typeclasses.solve
                                              #v_W
                                              proof
                                              writer
                                          in
                                          let writer:v_W = tmp0 in
                                          (match
                                              out
                                              <:
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error
                                            with
                                            | Core_models.Result.Result_Ok _ ->
                                              Core_models.Ops.Control_flow.ControlFlow_Continue
                                              writer
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Ops.Control_flow.t_ControlFlow
                                                    (v_W &
                                                      Core_models.Result.t_Result Prims.unit
                                                        Std.Io.Error.t_Error) (Prims.unit & v_W))
                                                v_W
                                            | Core_models.Result.Result_Err err ->
                                              Core_models.Ops.Control_flow.ControlFlow_Break
                                              (Core_models.Ops.Control_flow.ControlFlow_Break
                                                (writer,
                                                  (Core_models.Result.Result_Err err
                                                    <:
                                                    Core_models.Result.t_Result Prims.unit
                                                      Std.Io.Error.t_Error)
                                                  <:
                                                  (v_W &
                                                    Core_models.Result.t_Result Prims.unit
                                                      Std.Io.Error.t_Error))
                                                <:
                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                  (v_W &
                                                    Core_models.Result.t_Result Prims.unit
                                                      Std.Io.Error.t_Error) (Prims.unit & v_W))
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Ops.Control_flow.t_ControlFlow
                                                    (v_W &
                                                      Core_models.Result.t_Result Prims.unit
                                                        Std.Io.Error.t_Error) (Prims.unit & v_W))
                                                v_W)
                                        | Core_models.Result.Result_Err err ->
                                          Core_models.Ops.Control_flow.ControlFlow_Break
                                          (Core_models.Ops.Control_flow.ControlFlow_Break
                                            (writer,
                                              (Core_models.Result.Result_Err err
                                                <:
                                                Core_models.Result.t_Result Prims.unit
                                                  Std.Io.Error.t_Error)
                                              <:
                                              (v_W &
                                                Core_models.Result.t_Result Prims.unit
                                                  Std.Io.Error.t_Error))
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_W &
                                                Core_models.Result.t_Result Prims.unit
                                                  Std.Io.Error.t_Error) (Prims.unit & v_W))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (v_W &
                                                  Core_models.Result.t_Result Prims.unit
                                                    Std.Io.Error.t_Error) (Prims.unit & v_W)) v_W)
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (v_W &
                                      Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                                    v_W
                                with
                                | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                                | Core_models.Ops.Control_flow.ControlFlow_Continue writer ->
                                  let has_batch:bool =
                                    Core_models.Option.impl__is_some #Golden_rs.Zk_evrf.t_EVRFProof
                                      self.f_batch_evrf_proof
                                  in
                                  let
                                  (tmp0: v_W),
                                  (out: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                                  =
                                    Borsh.Ser.f_serialize #bool
                                      #FStar.Tactics.Typeclasses.solve
                                      #v_W
                                      has_batch
                                      writer
                                  in
                                  let writer:v_W = tmp0 in
                                  match
                                    out
                                    <:
                                    Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error
                                  with
                                  | Core_models.Result.Result_Ok _ ->
                                    (match
                                        self.f_batch_evrf_proof
                                        <:
                                        Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof
                                      with
                                      | Core_models.Option.Option_Some proof ->
                                        let
                                        (tmp0: v_W),
                                        (out:
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error) =
                                          Borsh.Ser.f_serialize #Golden_rs.Zk_evrf.t_EVRFProof
                                            #FStar.Tactics.Typeclasses.solve
                                            #v_W
                                            proof
                                            writer
                                        in
                                        let writer:v_W = tmp0 in
                                        (match
                                            out
                                            <:
                                            Core_models.Result.t_Result Prims.unit
                                              Std.Io.Error.t_Error
                                          with
                                          | Core_models.Result.Result_Ok _ ->
                                            let hax_temp_output:Core_models.Result.t_Result
                                              Prims.unit Std.Io.Error.t_Error =
                                              Core_models.Result.Result_Ok (() <: Prims.unit)
                                              <:
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error
                                            in
                                            writer, hax_temp_output
                                            <:
                                            (v_W &
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error)
                                          | Core_models.Result.Result_Err err ->
                                            writer,
                                            (Core_models.Result.Result_Err err
                                              <:
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error)
                                            <:
                                            (v_W &
                                              Core_models.Result.t_Result Prims.unit
                                                Std.Io.Error.t_Error))
                                      | _ ->
                                        let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                          Std.Io.Error.t_Error =
                                          Core_models.Result.Result_Ok (() <: Prims.unit)
                                          <:
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error
                                        in
                                        writer, hax_temp_output
                                        <:
                                        (v_W &
                                          Core_models.Result.t_Result Prims.unit
                                            Std.Io.Error.t_Error))
                                  | Core_models.Result.Result_Err err ->
                                    writer,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                                    <:
                                    (v_W &
                                      Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
                            | Core_models.Result.Result_Err err ->
                              writer,
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                              <:
                              (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
                      | Core_models.Result.Result_Err err ->
                        writer,
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                        <:
                        (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
                  | Core_models.Result.Result_Err err ->
                    writer,
                    (Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                    <:
                    (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
              | Core_models.Result.Result_Err err ->
                writer,
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
                <:
                (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
          | Core_models.Result.Result_Err err ->
            writer,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
            <:
            (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error))
      | Core_models.Result.Result_Err err ->
        writer,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        <:
        (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Borsh.De.t_BorshDeserialize t_Round0Msg =
  {
    f_deserialize_reader_pre
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
        (reader: v_R)
        ->
        true);
    f_deserialize_reader_post
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
        (reader: v_R)
        (out1: (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
        ->
        true);
    f_deserialize_reader
    =
    fun
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R)
      (reader: v_R)
      ->
      let
      (tmp0: v_R),
      (out: Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) Std.Io.Error.t_Error) =
        Borsh.De.f_deserialize_reader #(t_Array u8 (mk_usize 32))
          #FStar.Tactics.Typeclasses.solve
          #v_R
          reader
      in
      let reader:v_R = tmp0 in
      match out <: Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) Std.Io.Error.t_Error with
      | Core_models.Result.Result_Ok (session_id: t_Array u8 (mk_usize 32)) ->
        let (tmp0: v_R), (out: Core_models.Result.t_Result u32 Std.Io.Error.t_Error) =
          Borsh.De.f_deserialize_reader #u32 #FStar.Tactics.Typeclasses.solve #v_R reader
        in
        let reader:v_R = tmp0 in
        (match out <: Core_models.Result.t_Result u32 Std.Io.Error.t_Error with
          | Core_models.Result.Result_Ok (from: u32) ->
            let
            (tmp0: v_R),
            (out: Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) Std.Io.Error.t_Error) =
              Borsh.De.f_deserialize_reader #(t_Array u8 (mk_usize 32))
                #FStar.Tactics.Typeclasses.solve
                #v_R
                reader
            in
            let reader:v_R = tmp0 in
            (match
                out <: Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) Std.Io.Error.t_Error
              with
              | Core_models.Result.Result_Ok (random_msg: t_Array u8 (mk_usize 32)) ->
                let
                (tmp0: v_R),
                (out:
                  Core_models.Result.t_Result
                    (Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
                    Std.Io.Error.t_Error) =
                  Borsh.De.f_deserialize_reader #(Alloc.Vec.t_Vec
                        (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    #v_R
                    reader
                in
                let reader:v_R = tmp0 in
                (match
                    out
                    <:
                    Core_models.Result.t_Result
                      (Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                          Alloc.Alloc.t_Global) Std.Io.Error.t_Error
                  with
                  | Core_models.Result.Result_Ok
                    (commitment_bytes:
                      Alloc.Vec.t_Vec (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) Alloc.Alloc.t_Global
                    ) ->
                    let
                    (vss_commitment:
                      Alloc.Vec.t_Vec
                        (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                          Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
                      (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                        Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global =
                      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
                            (Core_models.Slice.Iter.t_Iter (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                            )
                            (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
                                -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config))
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec
                            (Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config) Alloc.Alloc.t_Global)
                        (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
                              (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                            #FStar.Tactics.Typeclasses.solve
                            #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                              Ark_bls12_381_.Curves.G1.t_Config)
                            #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
                                -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config)
                            (Core_models.Slice.impl__iter #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                                (Alloc.Vec.impl_1__as_slice commitment_bytes
                                  <:
                                  t_Slice (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                              <:
                              Core_models.Slice.Iter.t_Iter
                              (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                            (fun b ->
                                let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = b in
                                ark_from_bytes #(Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                    Ark_bls12_381_.Curves.G1.t_Config)
                                  (Alloc.Vec.impl_1__as_slice b <: t_Slice u8)
                                <:
                                Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                Ark_bls12_381_.Curves.G1.t_Config)
                          <:
                          Core_models.Iter.Adapters.Map.t_Map
                            (Core_models.Slice.Iter.t_Iter (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                            )
                            (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
                                -> Ark_ec.Models.Short_weierstrass.Affine.t_Affine
                                  Ark_bls12_381_.Curves.G1.t_Config))
                    in
                    let (tmp0: v_R), (out: Core_models.Result.t_Result u32 Std.Io.Error.t_Error) =
                      Borsh.De.f_deserialize_reader #u32
                        #FStar.Tactics.Typeclasses.solve
                        #v_R
                        reader
                    in
                    let reader:v_R = tmp0 in
                    (match out <: Core_models.Result.t_Result u32 Std.Io.Error.t_Error with
                      | Core_models.Result.Result_Ok (len: u32) ->
                        let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
                          t_Ciphertext
                          Std.Hash.Random.t_RandomState =
                          Std.Collections.Hash.Map.impl__new #u32 #t_Ciphertext ()
                        in
                        (match
                            Rust_primitives.Hax.Folds.fold_range_return (mk_u32 0)
                              len
                              (fun temp_0_ temp_1_ ->
                                  let
                                  (ciphertexts:
                                    Std.Collections.Hash.Map.t_HashMap u32
                                      t_Ciphertext
                                      Std.Hash.Random.t_RandomState),
                                  (reader: v_R) =
                                    temp_0_
                                  in
                                  let _:u32 = temp_1_ in
                                  true)
                              (ciphertexts, reader
                                <:
                                (Std.Collections.Hash.Map.t_HashMap u32
                                    t_Ciphertext
                                    Std.Hash.Random.t_RandomState &
                                  v_R))
                              (fun temp_0_ temp_1_ ->
                                  let
                                  (ciphertexts:
                                    Std.Collections.Hash.Map.t_HashMap u32
                                      t_Ciphertext
                                      Std.Hash.Random.t_RandomState),
                                  (reader: v_R) =
                                    temp_0_
                                  in
                                  let _:u32 = temp_1_ in
                                  let
                                  (tmp0: v_R),
                                  (out: Core_models.Result.t_Result u32 Std.Io.Error.t_Error) =
                                    Borsh.De.f_deserialize_reader #u32
                                      #FStar.Tactics.Typeclasses.solve
                                      #v_R
                                      reader
                                  in
                                  let reader:v_R = tmp0 in
                                  match
                                    out <: Core_models.Result.t_Result u32 Std.Io.Error.t_Error
                                  with
                                  | Core_models.Result.Result_Ok (node_id: u32) ->
                                    let
                                    (tmp0: v_R),
                                    (out:
                                      Core_models.Result.t_Result t_Ciphertext Std.Io.Error.t_Error)
                                    =
                                      Borsh.De.f_deserialize_reader #t_Ciphertext
                                        #FStar.Tactics.Typeclasses.solve
                                        #v_R
                                        reader
                                    in
                                    let reader:v_R = tmp0 in
                                    (match
                                        out
                                        <:
                                        Core_models.Result.t_Result t_Ciphertext
                                          Std.Io.Error.t_Error
                                      with
                                      | Core_models.Result.Result_Ok (ct: t_Ciphertext) ->
                                        let
                                        (tmp0:
                                          Std.Collections.Hash.Map.t_HashMap u32
                                            t_Ciphertext
                                            Std.Hash.Random.t_RandomState),
                                        (out: Core_models.Option.t_Option t_Ciphertext) =
                                          Std.Collections.Hash.Map.impl_2__insert #u32
                                            #t_Ciphertext
                                            #Std.Hash.Random.t_RandomState
                                            ciphertexts
                                            node_id
                                            ct
                                        in
                                        let ciphertexts:Std.Collections.Hash.Map.t_HashMap u32
                                          t_Ciphertext
                                          Std.Hash.Random.t_RandomState =
                                          tmp0
                                        in
                                        let _:Core_models.Option.t_Option t_Ciphertext = out in
                                        Core_models.Ops.Control_flow.ControlFlow_Continue
                                        (ciphertexts, reader
                                          <:
                                          (Std.Collections.Hash.Map.t_HashMap u32
                                              t_Ciphertext
                                              Std.Hash.Random.t_RandomState &
                                            v_R))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_R &
                                                Core_models.Result.t_Result t_Round0Msg
                                                  Std.Io.Error.t_Error)
                                              (Prims.unit &
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    t_Ciphertext
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R)))
                                          (Std.Collections.Hash.Map.t_HashMap u32
                                              t_Ciphertext
                                              Std.Hash.Random.t_RandomState &
                                            v_R)
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                          (reader,
                                            (Core_models.Result.Result_Err err
                                              <:
                                              Core_models.Result.t_Result t_Round0Msg
                                                Std.Io.Error.t_Error)
                                            <:
                                            (v_R &
                                              Core_models.Result.t_Result t_Round0Msg
                                                Std.Io.Error.t_Error))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (v_R &
                                              Core_models.Result.t_Result t_Round0Msg
                                                Std.Io.Error.t_Error)
                                            (Prims.unit &
                                              (Std.Collections.Hash.Map.t_HashMap u32
                                                  t_Ciphertext
                                                  Std.Hash.Random.t_RandomState &
                                                v_R)))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_R &
                                                Core_models.Result.t_Result t_Round0Msg
                                                  Std.Io.Error.t_Error)
                                              (Prims.unit &
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    t_Ciphertext
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R)))
                                          (Std.Collections.Hash.Map.t_HashMap u32
                                              t_Ciphertext
                                              Std.Hash.Random.t_RandomState &
                                            v_R))
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                      (reader,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error)
                                        <:
                                        (v_R &
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (v_R &
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error)
                                        (Prims.unit &
                                          (Std.Collections.Hash.Map.t_HashMap u32
                                              t_Ciphertext
                                              Std.Hash.Random.t_RandomState &
                                            v_R)))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (v_R &
                                            Core_models.Result.t_Result t_Round0Msg
                                              Std.Io.Error.t_Error)
                                          (Prims.unit &
                                            (Std.Collections.Hash.Map.t_HashMap u32
                                                t_Ciphertext
                                                Std.Hash.Random.t_RandomState &
                                              v_R)))
                                      (Std.Collections.Hash.Map.t_HashMap u32
                                          t_Ciphertext
                                          Std.Hash.Random.t_RandomState &
                                        v_R))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                              (Std.Collections.Hash.Map.t_HashMap u32
                                  t_Ciphertext
                                  Std.Hash.Random.t_RandomState &
                                v_R)
                          with
                          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                          | Core_models.Ops.Control_flow.ControlFlow_Continue (ciphertexts, reader) ->
                            let
                            (tmp0: v_R), (out: Core_models.Result.t_Result u32 Std.Io.Error.t_Error)
                            =
                              Borsh.De.f_deserialize_reader #u32
                                #FStar.Tactics.Typeclasses.solve
                                #v_R
                                reader
                            in
                            let reader:v_R = tmp0 in
                            match out <: Core_models.Result.t_Result u32 Std.Io.Error.t_Error with
                            | Core_models.Result.Result_Ok (proof_len: u32) ->
                              let evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
                                Golden_rs.Zk_evrf.t_EVRFProof
                                Std.Hash.Random.t_RandomState =
                                Std.Collections.Hash.Map.impl__new #u32
                                  #Golden_rs.Zk_evrf.t_EVRFProof
                                  ()
                              in
                              (match
                                  Rust_primitives.Hax.Folds.fold_range_return (mk_u32 0)
                                    proof_len
                                    (fun temp_0_ temp_1_ ->
                                        let
                                        (evrf_proofs:
                                          Std.Collections.Hash.Map.t_HashMap u32
                                            Golden_rs.Zk_evrf.t_EVRFProof
                                            Std.Hash.Random.t_RandomState),
                                        (reader: v_R) =
                                          temp_0_
                                        in
                                        let _:u32 = temp_1_ in
                                        true)
                                    (evrf_proofs, reader
                                      <:
                                      (Std.Collections.Hash.Map.t_HashMap u32
                                          Golden_rs.Zk_evrf.t_EVRFProof
                                          Std.Hash.Random.t_RandomState &
                                        v_R))
                                    (fun temp_0_ temp_1_ ->
                                        let
                                        (evrf_proofs:
                                          Std.Collections.Hash.Map.t_HashMap u32
                                            Golden_rs.Zk_evrf.t_EVRFProof
                                            Std.Hash.Random.t_RandomState),
                                        (reader: v_R) =
                                          temp_0_
                                        in
                                        let _:u32 = temp_1_ in
                                        let
                                        (tmp0: v_R),
                                        (out: Core_models.Result.t_Result u32 Std.Io.Error.t_Error)
                                        =
                                          Borsh.De.f_deserialize_reader #u32
                                            #FStar.Tactics.Typeclasses.solve
                                            #v_R
                                            reader
                                        in
                                        let reader:v_R = tmp0 in
                                        match
                                          out
                                          <:
                                          Core_models.Result.t_Result u32 Std.Io.Error.t_Error
                                        with
                                        | Core_models.Result.Result_Ok (node_id: u32) ->
                                          let
                                          (tmp0: v_R),
                                          (out:
                                            Core_models.Result.t_Result
                                              Golden_rs.Zk_evrf.t_EVRFProof Std.Io.Error.t_Error) =
                                            Borsh.De.f_deserialize_reader #Golden_rs.Zk_evrf.t_EVRFProof
                                              #FStar.Tactics.Typeclasses.solve
                                              #v_R
                                              reader
                                          in
                                          let reader:v_R = tmp0 in
                                          (match
                                              out
                                              <:
                                              Core_models.Result.t_Result
                                                Golden_rs.Zk_evrf.t_EVRFProof Std.Io.Error.t_Error
                                            with
                                            | Core_models.Result.Result_Ok
                                              (proof: Golden_rs.Zk_evrf.t_EVRFProof) ->
                                              let
                                              (tmp0:
                                                Std.Collections.Hash.Map.t_HashMap u32
                                                  Golden_rs.Zk_evrf.t_EVRFProof
                                                  Std.Hash.Random.t_RandomState),
                                              (out:
                                                Core_models.Option.t_Option
                                                Golden_rs.Zk_evrf.t_EVRFProof) =
                                                Std.Collections.Hash.Map.impl_2__insert #u32
                                                  #Golden_rs.Zk_evrf.t_EVRFProof
                                                  #Std.Hash.Random.t_RandomState
                                                  evrf_proofs
                                                  node_id
                                                  proof
                                              in
                                              let evrf_proofs:Std.Collections.Hash.Map.t_HashMap u32
                                                Golden_rs.Zk_evrf.t_EVRFProof
                                                Std.Hash.Random.t_RandomState =
                                                tmp0
                                              in
                                              let _:Core_models.Option.t_Option
                                              Golden_rs.Zk_evrf.t_EVRFProof =
                                                out
                                              in
                                              Core_models.Ops.Control_flow.ControlFlow_Continue
                                              (evrf_proofs, reader
                                                <:
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    Golden_rs.Zk_evrf.t_EVRFProof
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R))
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Ops.Control_flow.t_ControlFlow
                                                    (v_R &
                                                      Core_models.Result.t_Result t_Round0Msg
                                                        Std.Io.Error.t_Error)
                                                    (Prims.unit &
                                                      (Std.Collections.Hash.Map.t_HashMap u32
                                                          Golden_rs.Zk_evrf.t_EVRFProof
                                                          Std.Hash.Random.t_RandomState &
                                                        v_R)))
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    Golden_rs.Zk_evrf.t_EVRFProof
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R)
                                            | Core_models.Result.Result_Err err ->
                                              Core_models.Ops.Control_flow.ControlFlow_Break
                                              (Core_models.Ops.Control_flow.ControlFlow_Break
                                                (reader,
                                                  (Core_models.Result.Result_Err err
                                                    <:
                                                    Core_models.Result.t_Result t_Round0Msg
                                                      Std.Io.Error.t_Error)
                                                  <:
                                                  (v_R &
                                                    Core_models.Result.t_Result t_Round0Msg
                                                      Std.Io.Error.t_Error))
                                                <:
                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                  (v_R &
                                                    Core_models.Result.t_Result t_Round0Msg
                                                      Std.Io.Error.t_Error)
                                                  (Prims.unit &
                                                    (Std.Collections.Hash.Map.t_HashMap u32
                                                        Golden_rs.Zk_evrf.t_EVRFProof
                                                        Std.Hash.Random.t_RandomState &
                                                      v_R)))
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Ops.Control_flow.t_ControlFlow
                                                    (v_R &
                                                      Core_models.Result.t_Result t_Round0Msg
                                                        Std.Io.Error.t_Error)
                                                    (Prims.unit &
                                                      (Std.Collections.Hash.Map.t_HashMap u32
                                                          Golden_rs.Zk_evrf.t_EVRFProof
                                                          Std.Hash.Random.t_RandomState &
                                                        v_R)))
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    Golden_rs.Zk_evrf.t_EVRFProof
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R))
                                        | Core_models.Result.Result_Err err ->
                                          Core_models.Ops.Control_flow.ControlFlow_Break
                                          (Core_models.Ops.Control_flow.ControlFlow_Break
                                            (reader,
                                              (Core_models.Result.Result_Err err
                                                <:
                                                Core_models.Result.t_Result t_Round0Msg
                                                  Std.Io.Error.t_Error)
                                              <:
                                              (v_R &
                                                Core_models.Result.t_Result t_Round0Msg
                                                  Std.Io.Error.t_Error))
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (v_R &
                                                Core_models.Result.t_Result t_Round0Msg
                                                  Std.Io.Error.t_Error)
                                              (Prims.unit &
                                                (Std.Collections.Hash.Map.t_HashMap u32
                                                    Golden_rs.Zk_evrf.t_EVRFProof
                                                    Std.Hash.Random.t_RandomState &
                                                  v_R)))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (v_R &
                                                  Core_models.Result.t_Result t_Round0Msg
                                                    Std.Io.Error.t_Error)
                                                (Prims.unit &
                                                  (Std.Collections.Hash.Map.t_HashMap u32
                                                      Golden_rs.Zk_evrf.t_EVRFProof
                                                      Std.Hash.Random.t_RandomState &
                                                    v_R)))
                                            (Std.Collections.Hash.Map.t_HashMap u32
                                                Golden_rs.Zk_evrf.t_EVRFProof
                                                Std.Hash.Random.t_RandomState &
                                              v_R))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (v_R &
                                      Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                                    (Std.Collections.Hash.Map.t_HashMap u32
                                        Golden_rs.Zk_evrf.t_EVRFProof
                                        Std.Hash.Random.t_RandomState &
                                      v_R)
                                with
                                | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                                | Core_models.Ops.Control_flow.ControlFlow_Continue
                                  (evrf_proofs, reader) ->
                                  let
                                  (tmp0: v_R),
                                  (out: Core_models.Result.t_Result bool Std.Io.Error.t_Error) =
                                    Borsh.De.f_deserialize_reader #bool
                                      #FStar.Tactics.Typeclasses.solve
                                      #v_R
                                      reader
                                  in
                                  let reader:v_R = tmp0 in
                                  match
                                    out <: Core_models.Result.t_Result bool Std.Io.Error.t_Error
                                  with
                                  | Core_models.Result.Result_Ok (has_batch: bool) ->
                                    if has_batch
                                    then
                                      let
                                      (tmp0: v_R),
                                      (out:
                                        Core_models.Result.t_Result Golden_rs.Zk_evrf.t_EVRFProof
                                          Std.Io.Error.t_Error) =
                                        Borsh.De.f_deserialize_reader #Golden_rs.Zk_evrf.t_EVRFProof
                                          #FStar.Tactics.Typeclasses.solve
                                          #v_R
                                          reader
                                      in
                                      let reader:v_R = tmp0 in
                                      match
                                        out
                                        <:
                                        Core_models.Result.t_Result Golden_rs.Zk_evrf.t_EVRFProof
                                          Std.Io.Error.t_Error
                                      with
                                      | Core_models.Result.Result_Ok hoist59 ->
                                        let
                                        (reader: v_R),
                                        (batch_evrf_proof:
                                          Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof)
                                        =
                                          reader,
                                          (Core_models.Option.Option_Some hoist59
                                            <:
                                            Core_models.Option.t_Option
                                            Golden_rs.Zk_evrf.t_EVRFProof)
                                          <:
                                          (v_R &
                                            Core_models.Option.t_Option
                                            Golden_rs.Zk_evrf.t_EVRFProof)
                                        in
                                        let hax_temp_output:Core_models.Result.t_Result t_Round0Msg
                                          Std.Io.Error.t_Error =
                                          Core_models.Result.Result_Ok
                                          ({
                                              f_session_id = session_id;
                                              f_from = from;
                                              f_random_msg = random_msg;
                                              f_vss_commitment = vss_commitment;
                                              f_ciphertexts = ciphertexts;
                                              f_evrf_proofs = evrf_proofs;
                                              f_batch_evrf_proof = batch_evrf_proof
                                            }
                                            <:
                                            t_Round0Msg)
                                          <:
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error
                                        in
                                        reader, hax_temp_output
                                        <:
                                        (v_R &
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error)
                                      | Core_models.Result.Result_Err err ->
                                        reader,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error)
                                        <:
                                        (v_R &
                                          Core_models.Result.t_Result t_Round0Msg
                                            Std.Io.Error.t_Error)
                                    else
                                      let
                                      (reader: v_R),
                                      (batch_evrf_proof:
                                        Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof) =
                                        reader,
                                        (Core_models.Option.Option_None
                                          <:
                                          Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof)
                                        <:
                                        (v_R &
                                          Core_models.Option.t_Option Golden_rs.Zk_evrf.t_EVRFProof)
                                      in
                                      let hax_temp_output:Core_models.Result.t_Result t_Round0Msg
                                        Std.Io.Error.t_Error =
                                        Core_models.Result.Result_Ok
                                        ({
                                            f_session_id = session_id;
                                            f_from = from;
                                            f_random_msg = random_msg;
                                            f_vss_commitment = vss_commitment;
                                            f_ciphertexts = ciphertexts;
                                            f_evrf_proofs = evrf_proofs;
                                            f_batch_evrf_proof = batch_evrf_proof
                                          }
                                          <:
                                          t_Round0Msg)
                                        <:
                                        Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error
                                      in
                                      reader, hax_temp_output
                                      <:
                                      (v_R &
                                        Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error
                                      )
                                  | Core_models.Result.Result_Err err ->
                                    reader,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                                    <:
                                    (v_R &
                                      Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
                            | Core_models.Result.Result_Err err ->
                              reader,
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                              <:
                              (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
                      | Core_models.Result.Result_Err err ->
                        reader,
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                        <:
                        (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
                  | Core_models.Result.Result_Err err ->
                    reader,
                    (Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                    <:
                    (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
              | Core_models.Result.Result_Err err ->
                reader,
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
                <:
                (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
          | Core_models.Result.Result_Err err ->
            reader,
            (Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
            <:
            (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error))
      | Core_models.Result.Result_Err err ->
        reader,
        (Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
        <:
        (v_R & Core_models.Result.t_Result t_Round0Msg Std.Io.Error.t_Error)
  }

/// Reshare broadcast message from an old-group member to the new group.
/// Structurally similar to [`Round0Msg`] but without eVRF proofs (the reshare
/// protocol relies on VSS commitment verification against known public key shares
/// instead).
type t_ReshareMsg = {
  f_session_id:t_Array u8 (mk_usize 32);
  f_from:u32;
  f_random_msg:t_Array u8 (mk_usize 32);
  f_vss_commitment:Alloc.Vec.t_Vec
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Alloc.Alloc.t_Global;
  f_ciphertexts:Std.Collections.Hash.Map.t_HashMap u32 t_Ciphertext Std.Hash.Random.t_RandomState
}

let impl_11: Core_models.Clone.t_Clone t_ReshareMsg =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Fmt.t_Debug t_ReshareMsg

unfold
let impl_12 = impl_12'

/// Output of the DKG protocol for a single node.
/// Per Round 1 line 17 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "return (PK, {PK_j}, sk_i)"
/// Contains the shared public key, per-participant public key shares, and
/// this node's secret key share.
type t_DkgOutput = {
  f_public_key:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_public_key_shares:Std.Collections.Hash.Map.t_HashMap u32
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)
    Std.Hash.Random.t_RandomState;
  f_secret_share:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4)
}

let impl_13: Core_models.Clone.t_Clone t_DkgOutput =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Fmt.t_Debug t_DkgOutput

unfold
let impl_14 = impl_14'
