module Tracing_core.Metadata

/// Tracing metadata as opaque type.
assume new type t_Metadata : Type0

/// Re-export t_Level from Callsite (extraction references it as both
/// Tracing_core.Callsite.t_Level and Tracing_core.Metadata.t_Level).
let t_Level = Tracing_core.Callsite.t_Level

/// Metadata::new() and Level constants
assume val impl__new : #v_A:Type0 -> #v_B:Type0 -> #v_C:Type0 -> #v_D:Type0
  -> #v_E:Type0 -> #v_F:Type0 -> #v_G:Type0 -> #v_H:Type0 -> v_A -> v_B -> v_C
  -> v_D -> v_E -> v_F -> v_G -> v_H -> t_Metadata

assume val impl_Level__WARN : Tracing_core.Callsite.t_Level
assume val impl_Level__INFO : Tracing_core.Callsite.t_Level
assume val impl_Level__ERROR : Tracing_core.Callsite.t_Level
assume val impl_Level__DEBUG : Tracing_core.Callsite.t_Level
assume val impl_Level__TRACE : Tracing_core.Callsite.t_Level

assume new type t_LevelFilter : Type0
assume val impl_LevelFilter__current : Prims.unit -> t_LevelFilter

assume new type t_Kind : Type0
assume val impl_Kind__EVENT : t_Kind

assume val impl__fields : t_Metadata -> Tracing_core.Field.t_FieldSet
