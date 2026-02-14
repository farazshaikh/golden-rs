module Borsh.Ser

open Rust_primitives

class t_BorshSerialize (v_Self: Type0) = {
  f_serialize_pre:
      (#v_W: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W) ->
      v_Self ->
      v_W ->
      Type0;
  f_serialize_post:
      (#v_W: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W) ->
      v_Self ->
      v_W ->
      (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) ->
      Type0;
  f_serialize:
      (#v_W: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Write v_W) ->
      v_Self ->
      v_W ->
      (v_W & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error);
}

/// Typeclass instances for primitive types used in serialization.
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_ser_u32 : t_BorshSerialize u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_ser_bool : t_BorshSerialize bool

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_ser_vec (#v_T: Type0) (#v_A: Type0) : t_BorshSerialize (Alloc.Vec.t_Vec v_T v_A)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_ser_array (#v_T: Type0) (#n: usize) : t_BorshSerialize (t_Array v_T n)
