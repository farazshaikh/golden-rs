module Tokio.Sync.Rwlock

/// Stub model for tokio::sync::RwLock.

assume new type t_RwLock (v_T: Type0) : Type0

/// RwLock::new(value) -> RwLock<T>
assume val impl_14__new (#v_T: Type0) (value: v_T) : t_RwLock v_T
