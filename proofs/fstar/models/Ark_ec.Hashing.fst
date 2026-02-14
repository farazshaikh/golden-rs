module Ark_ec.Hashing
open Rust_primitives

assume new type t_HashToCurveError : Type0

assume val f_new : #proj:Type0 -> #hasher:Type0 -> #mapper:Type0 -> t_Slice u8 -> Core_models.Result.t_Result (Ark_ec.Hashing.Map_to_curve_hasher.t_MapToCurveBasedHasher proj hasher mapper) t_HashToCurveError

open Ark_ec.Models.Short_weierstrass.Affine
assume val f_hash : #proj:Type0 -> #hasher:Type0 -> #mapper:Type0 -> Ark_ec.Hashing.Map_to_curve_hasher.t_MapToCurveBasedHasher proj hasher mapper -> Rust_primitives.t_Slice Rust_primitives.Integers.u8 -> Core_models.Result.t_Result (t_Affine Ark_bls12_381_.Curves.G1.t_Config) t_HashToCurveError
