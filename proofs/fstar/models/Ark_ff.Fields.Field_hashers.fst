module Ark_ff.Fields.Field_hashers

/// DefaultFieldHasher takes the hasher type AND a security parameter (usize).
assume new type t_DefaultFieldHasher (hasher : Type0) (security_param : Rust_primitives.Integers.usize) : Type0
