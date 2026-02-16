module Golden_dkg.Threshold.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Information about the threshold group derived from DKG output.
/// Contains the shared public key and the BFT parameters (threshold, group size).
type t_GroupInfo = {
  f_public_key:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config;
  f_threshold:u32;
  f_num_nodes:u32
}

let impl: Core_models.Clone.t_Clone t_GroupInfo =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Fmt.t_Debug t_GroupInfo

unfold
let impl_1 = impl_1'

/// A single node's share of the group secret key.
/// Each node holds one `KeyShare` after DKG completes.  Any `threshold`
/// nodes can combine their partial signatures into a full threshold signature.
type t_KeyShare = {
  f_id:u32;
  f_secret:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig
        (mk_usize 4)) (mk_usize 4);
  f_group_info:t_GroupInfo
}

let impl_2: Core_models.Clone.t_Clone t_KeyShare =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_KeyShare

unfold
let impl_3 = impl_3'

/// A partial BLS signature produced by a single signer.
/// Created by [`crate::signing::partial_sign`]. Collect at least `threshold`
/// of these and pass them to [`crate::signing::combine`] to get a
/// [`ThresholdSignature`].
type t_PartialSignature = {
  f_signer:u32;
  f_signature:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
}

let impl_4: Core_models.Clone.t_Clone t_PartialSignature =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_PartialSignature

unfold
let impl_5 = impl_5'

/// A combined threshold BLS signature.
/// Produced by [`crate::signing::combine`] from `>= threshold` partial
/// signatures.  Verifiable against the group public key via
/// [`crate::signing::verify`].
type t_ThresholdSignature = {
  f_signature:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G2.t_Config
}

let impl_6: Core_models.Clone.t_Clone t_ThresholdSignature =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Fmt.t_Debug t_ThresholdSignature

unfold
let impl_7 = impl_7'

/// A random beacon output for a single round.
/// Compatible with the [drand](https://drand.love/) beacon wire format.
/// Each beacon contains a deterministic signature over the round number
/// (and optionally the previous signature), plus derived randomness.
type t_Beacon = {
  f_round:u64;
  f_previous_signature:Core_models.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global);
  f_signature:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_randomness:t_Array u8 (mk_usize 32)
}

let impl_8: Core_models.Clone.t_Clone t_Beacon =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Fmt.t_Debug t_Beacon

unfold
let impl_9 = impl_9'

/// Beacon chaining mode.
/// Determines how the message to sign is constructed each round.
type t_BeaconMode =
  | BeaconMode_Chained : t_BeaconMode
  | BeaconMode_Unchained : t_BeaconMode

let t_BeaconMode_cast_to_repr (x: t_BeaconMode) : isize =
  match x <: t_BeaconMode with
  | BeaconMode_Chained  -> mk_isize 0
  | BeaconMode_Unchained  -> mk_isize 1

let impl_10: Core_models.Clone.t_Clone t_BeaconMode =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core_models.Marker.t_Copy t_BeaconMode

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Fmt.t_Debug t_BeaconMode

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core_models.Marker.t_StructuralPartialEq t_BeaconMode

unfold
let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Cmp.t_PartialEq t_BeaconMode t_BeaconMode

unfold
let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core_models.Cmp.t_Eq t_BeaconMode

unfold
let impl_15 = impl_15'
