module Tokio.Sync.Broadcast

/// Stub model for tokio::sync::broadcast channel.

open Rust_primitives
open Core_models

assume new type t_Sender (v_T: Type0) : Type0
assume new type t_Receiver (v_T: Type0) : Type0

/// broadcast::channel(capacity) -> (Sender, Receiver)
assume val channel (#v_T: Type0) (capacity: usize) : (t_Sender v_T & t_Receiver v_T)

/// Sender::send(msg) -> Result<usize, SendError>
assume val impl_3__send (#v_T: Type0)
  (s: t_Sender v_T) (msg: v_T)
  : Core_models.Result.t_Result usize (Tokio.Sync.Broadcast.Error.t_SendError v_T)
