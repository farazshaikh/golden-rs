module Ark_serialize

open Rust_primitives

class t_CanonicalSerialize (v_Self: Type0) = {
  __canon_ser_dummy: bool;
}

class t_CanonicalDeserialize (v_Self: Type0) = {
  __canon_de_dummy: bool;
}

/// Blanket instances for any type
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_canon_ser_blanket (#v_T: Type0) : t_CanonicalSerialize v_T
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_canon_de_blanket (#v_T: Type0) : t_CanonicalDeserialize v_T

/// f_serialize_compressed: used by ark_to_bytes via Hax.failure (body is opaque).
/// f_deserialize_compressed: called as
///   Ark_serialize.f_deserialize_compressed #T #solve #Reader data
/// Returns Result T SerializationError.
assume val f_deserialize_compressed
  (#v_T: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_CanonicalDeserialize v_T)
  (#v_R: Type0)
  (reader: v_R)
  : Core_models.Result.t_Result v_T Ark_serialize.Error.t_SerializationError

assume val f_serialize_compressed
  (#v_T: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_CanonicalSerialize v_T)
  (#v_W: Type0)
  (value: v_T)
  (writer: v_W)
  : Core_models.Result.t_Result Prims.unit Ark_serialize.Error.t_SerializationError
