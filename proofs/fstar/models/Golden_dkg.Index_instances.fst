module Golden_dkg.Index_instances

/// Index instances for slice indexing used by golden-rs extraction.
/// shares[i] desugars to Core_models.Ops.Index.f_index shares i.

open Rust_primitives
open Core_models.Ops.Index

/// Index instance for t_Slice T indexed by usize -> returns T
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_index_slice_usize (#v_T: Type0)
  : t_Index (t_Slice v_T) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (s: t_Slice v_T) (i: usize) -> true);
    f_index_post = (fun (s: t_Slice v_T) (i: usize) (out: v_T) -> true);
    f_index = (fun (s: t_Slice v_T) (i: usize) ->
      Rust_primitives.Sequence.seq_index #v_T s (Rust_primitives.Integers.v i));
  }

/// Index instance for Vec T indexed by usize -> returns T
/// Needed when hax generates `vec.[i]` instead of `(as_slice vec).[i]`.
open Alloc.Vec
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_index_vec_usize (#v_T: Type0)
  : t_Index (t_Vec v_T Alloc.Alloc.t_Global) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (s: t_Vec v_T Alloc.Alloc.t_Global) (i: usize) -> true);
    f_index_post = (fun (s: t_Vec v_T Alloc.Alloc.t_Global) (i: usize) (out: v_T) -> true);
    f_index = (fun (s: t_Vec v_T Alloc.Alloc.t_Global) (i: usize) ->
      Rust_primitives.Sequence.seq_index #v_T (Alloc.Vec.impl_1__as_slice s) (Rust_primitives.Integers.v i));
  }
