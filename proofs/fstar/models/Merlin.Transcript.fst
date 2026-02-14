module Merlin.Transcript

open Rust_primitives

assume new type t_Transcript : Type0

assume val impl_Transcript__new : #v_T:Type0 -> v_T -> t_Transcript
