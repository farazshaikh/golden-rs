module Golden_dkg.Consensus.Vrf
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Block_buffer in
  let open Digest in
  let open Digest.Core_api in
  let open Digest.Core_api.Ct_variable in
  let open Digest.Core_api.Wrapper in
  let open Digest.Digest in
  let open Generic_array in
  let open Sha2.Core_api in
  let open Typenum in
  let open Typenum.Bit in
  let open Typenum.Marker_traits in
  let open Typenum.Private in
  let open Typenum.Type_operators in
  let open Typenum.Uint in
  ()

/// Construct the VRF message bytes for a given view.
/// The message is deterministic per view:
/// `"simplex-vrf-v1" || view.to_be_bytes()`
let vrf_message (view: u64) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec #u8
      ((let list =
            [
              mk_u8 115; mk_u8 105; mk_u8 109; mk_u8 112; mk_u8 108; mk_u8 101; mk_u8 120; mk_u8 45;
              mk_u8 118; mk_u8 114; mk_u8 102; mk_u8 45; mk_u8 118; mk_u8 49
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 14);
          Rust_primitives.Hax.array_of_list 14 list)
        <:
        t_Slice u8)
  in
  let msg:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      msg
      (Core_models.Num.impl_u64__to_be_bytes view <: t_Slice u8)
  in
  msg

/// Elect a leader from a VRF seed.
/// Paper: "L_h := H*(h) mod n" (1-indexed NodeId).
/// The VRF seed is the randomness derived from the previous view's
/// combined threshold signature (either notarization or nullification).
let elect_leader (vrf_seed: t_Slice u8) (n: u32) : u32 =
  let hash:Generic_array.t_GenericArray u8
    (Typenum.Uint.t_UInt
        (Typenum.Uint.t_UInt
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
        Typenum.Bit.t_B0) =
    Digest.Digest.f_digest #(Digest.Core_api.Wrapper.t_CoreWrapper
        (Digest.Core_api.Ct_variable.t_CtVariableCoreWrapper Sha2.Core_api.t_Sha256VarCore
            (Typenum.Uint.t_UInt
                (Typenum.Uint.t_UInt
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                    Typenum.Bit.t_B0) Typenum.Bit.t_B0)
            Sha2.t_OidSha256))
      #FStar.Tactics.Typeclasses.solve
      #(t_Slice u8)
      vrf_seed
  in
  let v_val:u32 =
    Core_models.Num.impl_u32__from_be_bytes (let list =
          [
            (Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                            Typenum.Bit.t_B0) Typenum.Bit.t_B0))
                #FStar.Tactics.Typeclasses.solve
                hash
              <:
              t_Slice u8).[ mk_usize 0 ]
            <:
            u8;
            (Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                            Typenum.Bit.t_B0) Typenum.Bit.t_B0))
                #FStar.Tactics.Typeclasses.solve
                hash
              <:
              t_Slice u8).[ mk_usize 1 ]
            <:
            u8;
            (Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                            Typenum.Bit.t_B0) Typenum.Bit.t_B0))
                #FStar.Tactics.Typeclasses.solve
                hash
              <:
              t_Slice u8).[ mk_usize 2 ]
            <:
            u8;
            (Core_models.Ops.Deref.f_deref #(Generic_array.t_GenericArray u8
                    (Typenum.Uint.t_UInt
                        (Typenum.Uint.t_UInt
                            (Typenum.Uint.t_UInt
                                (Typenum.Uint.t_UInt
                                    (Typenum.Uint.t_UInt
                                        (Typenum.Uint.t_UInt Typenum.Uint.t_UTerm Typenum.Bit.t_B1)
                                        Typenum.Bit.t_B0) Typenum.Bit.t_B0) Typenum.Bit.t_B0)
                            Typenum.Bit.t_B0) Typenum.Bit.t_B0))
                #FStar.Tactics.Typeclasses.solve
                hash
              <:
              t_Slice u8).[ mk_usize 3 ]
            <:
            u8
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  (v_val %! n <: u32) +! mk_u32 1
