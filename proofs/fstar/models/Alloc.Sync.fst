module Alloc.Sync

/// Stub model for std::sync::Arc.

assume new type t_Arc (v_T: Type0) (v_A: Type0) : Type0

/// Arc::new(value) -> Arc<T>
assume val impl_16__new (#v_T: Type0) (value: v_T) : t_Arc v_T Alloc.Alloc.t_Global
