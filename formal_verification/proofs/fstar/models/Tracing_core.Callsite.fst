module Tracing_core.Callsite

/// Tracing callsite and level types.
/// No dependencies on other Tracing_core modules to avoid cycles.
assume new type t_Callsite : Type0
assume new type t_Level : Type0
assume new type t_DefaultCallsite : Type0
/// Identifier is a DATA CONSTRUCTOR in the extraction.
type t_Identifier = | Identifier : #v_T:Type0 -> v_T -> t_Identifier

/// These functions take/return opaque types to avoid circular deps.
assume val impl_DefaultCallsite__new : #v_M:Type0 -> v_M -> t_DefaultCallsite
assume val impl_DefaultCallsite__interest : #v_I:Type0 -> t_DefaultCallsite -> v_I
assume val f_metadata : #v_T:Type0 -> #v_M:Type0 -> v_T -> v_M
