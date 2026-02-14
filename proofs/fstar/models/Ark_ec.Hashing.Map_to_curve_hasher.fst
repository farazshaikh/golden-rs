module Ark_ec.Hashing.Map_to_curve_hasher

/// Hash-to-curve hasher type (opaque -- treated as random oracle in proofs).
assume new type t_MapToCurveBasedHasher (proj : Type0) (hasher : Type0) (mapper : Type0) : Type0
