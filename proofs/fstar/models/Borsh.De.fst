module Borsh.De

open Rust_primitives

class t_BorshDeserialize (v_Self: Type0) = {
  f_deserialize_reader_pre:
      (#v_R: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R) ->
      v_R ->
      Type0;
  f_deserialize_reader_post:
      (#v_R: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R) ->
      v_R ->
      (v_R & Core_models.Result.t_Result v_Self Std.Io.Error.t_Error) ->
      Type0;
  f_deserialize_reader:
      (#v_R: Type0) ->
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Std.Io.t_Read v_R) ->
      v_R ->
      (v_R & Core_models.Result.t_Result v_Self Std.Io.Error.t_Error);
}

/// Typeclass instances for primitive types used in deserialization.
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_de_u32 : t_BorshDeserialize u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_de_bool : t_BorshDeserialize bool

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_de_vec (#v_T: Type0) (#v_A: Type0) : t_BorshDeserialize (Alloc.Vec.t_Vec v_T v_A)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_borsh_de_array (#v_T: Type0) (#n: usize) : t_BorshDeserialize (t_Array v_T n)
