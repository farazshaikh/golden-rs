module Ark_ec.Hashing.Map_to_curve_hasher

/// Hash-to-curve hasher type (opaque -- treated as random oracle in proofs).
assume new type t_MapToCurveBasedHasher (proj : Type0) (hasher : Type0) (mapper : Type0) : Type0

assume val impl_1__new_ref : #t1:Type0 -> #t2:Type0 -> #t3:Type0 -> t1 -> t2 -> Ark_ec.Hashing.Map_to_curve_hasher.t_MapToCurveBasedHasher t1 t2 t3
