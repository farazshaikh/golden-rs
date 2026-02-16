module Ark_ff.Fields.Models.Fp.Montgomery_backend

open Rust_primitives

/// Stub for arkworks Montgomery-form field backend.
/// This is a type-level parameter -- it carries the field configuration
/// but has no runtime representation of its own.

assume new type t_MontBackend (config : Type0) (n : usize) : Type0
