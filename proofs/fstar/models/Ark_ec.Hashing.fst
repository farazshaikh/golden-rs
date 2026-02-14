module Ark_ec.Hashing
open Rust_primitives

assume new type t_HashToCurveError : Type0

/// HashToCurve trait (for tcresolve in f_new/f_hash calls)
class t_HashToCurve (v_Self : Type0) = { __htc_dummy : unit; }
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_htc_blanket (#v_T: Type0) : t_HashToCurve v_T

/// f_new: hax calls with #OutputType #GroupType #solve domain
assume val f_new : #v_Self:Type0 -> #v_Group:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_HashToCurve v_Self
  -> t_Slice u8 -> Core_models.Result.t_Result v_Self t_HashToCurveError

open Ark_ec.Models.Short_weierstrass.Affine
/// f_hash: hax calls with #HasherType #GroupType #solve hasher msg
assume val f_hash : #v_Self:Type0 -> #v_Group:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_HashToCurve v_Self
  -> v_Self -> Rust_primitives.t_Slice Rust_primitives.Integers.u8
  -> Core_models.Result.t_Result (t_Affine Ark_bls12_381_.Curves.G1.t_Config) t_HashToCurveError
