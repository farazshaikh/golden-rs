module Ark_r1cs_std.Convert

open Rust_primitives
assume val f_to_bits_le : #a:Type0 -> #b:Type0 -> a -> Alloc.Vec.t_Vec b Alloc.Alloc.t_Global
