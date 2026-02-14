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
assume
val impl_3: Borsh.Ser.t_BorshSerialize t_Ciphertext

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4: Borsh.De.t_BorshDeserialize t_Ciphertext

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
assume
val impl_5: Borsh.Ser.t_BorshSerialize t_Round0Msg

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6: Borsh.De.t_BorshDeserialize t_Round0Msg

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
