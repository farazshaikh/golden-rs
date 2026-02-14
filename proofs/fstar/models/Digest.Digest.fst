module Digest.Digest

open Rust_primitives

class t_Digest (v_Self: Type0) = {
  __digest_dummy: bool;
}

assume val f_new (#v_T: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_Digest v_T)
  (x: Prims.unit)
  : v_T

assume val f_update (#v_T: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_Digest v_T)
  (#v_D: Type0)
  (h: v_T) (d: v_D)
  : v_T

/// SHA-256 output size as typenum: binary 100000 = 32
let typenum_32 : Type0 =
  Typenum.Uint.t_UInt
    (Typenum.Uint.t_UInt
      (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
          (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
            Typenum.Bit.t_B0)
          Typenum.Bit.t_B0)
        Typenum.Bit.t_B0)
      Typenum.Bit.t_B0)
    Typenum.Bit.t_B0

/// f_finalize output type: GenericArray<u8, U32> for SHA-256.
/// All digest uses in golden-rs are SHA-256 (32-byte output).
/// This concrete type alias lets F* unify with the extraction's expected type.
let t_DigestOutput : Type0 = Generic_array.t_GenericArray Rust_primitives.Integers.u8 typenum_32

assume val f_finalize (#v_T: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_Digest v_T)
  (h: v_T)
  : t_DigestOutput

/// Instance for CoreWrapper types (SHA-256, etc.)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_digest_corewrapper (#inner: Type0) : t_Digest (Digest.Core_api.Wrapper.t_CoreWrapper inner)
