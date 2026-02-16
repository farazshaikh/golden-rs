module Tracing_core.Field

/// Stub models for tracing field/value types.

assume new type t_FieldSet : Type0
assume new type t_Value : Type0
assume new type t_ValueSet : Type0

assume val impl_FieldSet__new : #v_A:Type0 -> v_A -> t_FieldSet
assume val impl_FieldSet__value_set_all : #v_A:Type0 -> #v_B:Type0 -> v_A -> v_B -> t_ValueSet
