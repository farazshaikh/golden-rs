module Golden_dkg.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Error type for DKG and refresh protocol operations.
/// Returned by functions in [`crate::dkg`] and [`crate::refresh`].
/// Verification errors (ciphertext, proof, session) indicate a malicious or
/// misbehaving participant whose dealing should be rejected.
type t_DkgError =
  | DkgError_CiphertextVerificationFailed {
    f_sender:u32;
    f_recipient:u32
  }: t_DkgError
  | DkgError_MissingCiphertext {
    f_sender:u32;
    f_recipient:u32
  }: t_DkgError
  | DkgError_ZeroSecretViolation { f_sender:u32 }: t_DkgError
  | DkgError_PeerCountMismatch {
    f_expected:u32;
    f_got:usize
  }: t_DkgError
  | DkgError_BroadcastReceiveFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_DkgError
  | DkgError_RegistrationFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_DkgError
  | DkgError_SessionMismatch { f_sender:u32 }: t_DkgError
  | DkgError_ProofError : Alloc.String.t_String -> t_DkgError

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Fmt.t_Debug t_DkgError

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Fmt.t_Display t_DkgError =
  {
    f_fmt_pre = (fun (self: t_DkgError) (f: Core_models.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_DkgError)
        (f: Core_models.Fmt.t_Formatter)
        (out1:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_DkgError) (f: Core_models.Fmt.t_Formatter) ->
      let args:t_DkgError = self <: t_DkgError in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_debug #t_DkgError args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let
      (tmp0: Core_models.Fmt.t_Formatter),
      (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
        Core_models.Fmt.impl_11__write_fmt f
          (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
              (mk_usize 1)
              (let list = [""] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let f:Core_models.Fmt.t_Formatter = tmp0 in
      let hax_temp_output:Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error = out in
      f, hax_temp_output
      <:
      (Core_models.Fmt.t_Formatter & Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Error.t_Error t_DkgError =
  { _super_i0 = FStar.Tactics.Typeclasses.solve; _super_i1 = FStar.Tactics.Typeclasses.solve }

/// Error type for membership-change resharing operations.
/// Returned by functions in [`crate::reshare`]. These errors cover both the
/// old member's dealing creation and the new member's completion phase.
type t_ReshareError =
  | ReshareError_CiphertextVerificationFailed {
    f_sender:u32;
    f_recipient:u32
  }: t_ReshareError
  | ReshareError_MissingCiphertext {
    f_sender:u32;
    f_recipient:u32
  }: t_ReshareError
  | ReshareError_InsufficientDealers {
    f_needed:u32;
    f_got:u32
  }: t_ReshareError
  | ReshareError_BroadcastReceiveFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_ReshareError
  | ReshareError_RegistrationFailed {
    f_node:u32;
    f_reason:Alloc.String.t_String
  }: t_ReshareError
  | ReshareError_DuplicateNodeIndex { f_index:u32 }: t_ReshareError
  | ReshareError_NoMessages : t_ReshareError
  | ReshareError_SessionMismatch { f_sender:u32 }: t_ReshareError

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_ReshareError

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Fmt.t_Display t_ReshareError =
  {
    f_fmt_pre = (fun (self: t_ReshareError) (f: Core_models.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_ReshareError)
        (f: Core_models.Fmt.t_Formatter)
        (out1:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_ReshareError) (f: Core_models.Fmt.t_Formatter) ->
      let args:t_ReshareError = self <: t_ReshareError in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_debug #t_ReshareError args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let
      (tmp0: Core_models.Fmt.t_Formatter),
      (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
        Core_models.Fmt.impl_11__write_fmt f
          (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
              (mk_usize 1)
              (let list = [""] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let f:Core_models.Fmt.t_Formatter = tmp0 in
      let hax_temp_output:Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error = out in
      f, hax_temp_output
      <:
      (Core_models.Fmt.t_Formatter & Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Error.t_Error t_ReshareError =
  { _super_i0 = FStar.Tactics.Typeclasses.solve; _super_i1 = FStar.Tactics.Typeclasses.solve }
