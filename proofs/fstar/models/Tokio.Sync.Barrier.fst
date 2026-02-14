module Tokio.Sync.Barrier

/// Stub model for tokio::sync::Barrier.

open Rust_primitives

assume new type t_Barrier : Type0

assume val impl_Barrier__new (count: usize) : t_Barrier
