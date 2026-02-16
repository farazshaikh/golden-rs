module Golden_dkg.Threshold.Dkg
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Golden_dkg.Threshold.Types in
  ()

/// Convert raw DKG outputs into threshold-crypto key shares and group info.
/// Takes the `(NodeId, DkgOutput)` pairs produced by `golden_dkg` and
/// extracts the secret shares and shared public key into this crate's types.
/// # Panics
/// Panics if `dkg_outputs` is empty.
let bootstrap (dkg_outputs: t_Slice (u32 & Golden_dkg.Types.t_DkgOutput)) (t: u32)
    : (Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_KeyShare Alloc.Alloc.t_Global &
      Golden_dkg.Threshold.Types.t_GroupInfo) =
  let _:Prims.unit =
    if
      ~.(~.(Core_models.Slice.impl__is_empty #(u32 & Golden_dkg.Types.t_DkgOutput) dkg_outputs
          <:
          bool)
        <:
        bool)
    then
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic_fmt (Core_models.Fmt.Rt.impl_1__new_const
                (mk_usize 1)
                (let list = ["need at least one DKG output"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core_models.Fmt.t_Arguments)
          <:
          Rust_primitives.Hax.t_Never)
  in
  let n:u32 =
    cast (Core_models.Slice.impl__len #(u32 & Golden_dkg.Types.t_DkgOutput) dkg_outputs <: usize)
    <:
    u32
  in
  let pk:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config =
    (dkg_outputs.[ mk_usize 0 ])._2.Golden_dkg.Types.f_public_key
  in
  let group_info:Golden_dkg.Threshold.Types.t_GroupInfo =
    {
      Golden_dkg.Threshold.Types.f_public_key = pk;
      Golden_dkg.Threshold.Types.f_threshold = t;
      Golden_dkg.Threshold.Types.f_num_nodes = n
    }
    <:
    Golden_dkg.Threshold.Types.t_GroupInfo
  in
  let shares:Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_KeyShare Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Types.t_DkgOutput))
          ((u32 & Golden_dkg.Types.t_DkgOutput) -> Golden_dkg.Threshold.Types.t_KeyShare))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_KeyShare Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
            (u32 & Golden_dkg.Types.t_DkgOutput))
          #FStar.Tactics.Typeclasses.solve
          #Golden_dkg.Threshold.Types.t_KeyShare
          #((u32 & Golden_dkg.Types.t_DkgOutput) -> Golden_dkg.Threshold.Types.t_KeyShare)
          (Core_models.Slice.impl__iter #(u32 & Golden_dkg.Types.t_DkgOutput) dkg_outputs
            <:
            Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Types.t_DkgOutput))
          (fun temp_0_ ->
              let (id: u32), (out: Golden_dkg.Types.t_DkgOutput) = temp_0_ in
              {
                Golden_dkg.Threshold.Types.f_id = id;
                Golden_dkg.Threshold.Types.f_secret = out.Golden_dkg.Types.f_secret_share;
                Golden_dkg.Threshold.Types.f_group_info
                =
                Core_models.Clone.f_clone #Golden_dkg.Threshold.Types.t_GroupInfo
                  #FStar.Tactics.Typeclasses.solve
                  group_info
                <:
                Golden_dkg.Threshold.Types.t_GroupInfo
              }
              <:
              Golden_dkg.Threshold.Types.t_KeyShare)
        <:
        Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter (u32 & Golden_dkg.Types.t_DkgOutput))
          ((u32 & Golden_dkg.Types.t_DkgOutput) -> Golden_dkg.Threshold.Types.t_KeyShare))
  in
  shares, group_info
  <:
  (Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_KeyShare Alloc.Alloc.t_Global &
    Golden_dkg.Threshold.Types.t_GroupInfo)

/// Run a full DKG ceremony and return threshold-crypto types.
/// Convenience function that executes the complete golden-dkg protocol
/// (create dealings + complete) with `n` participants and threshold `t`,
/// then converts the output.
/// Uses rayon for parallel dealing creation and completion.
let run_dkg (n t: u32)
    : (Alloc.Vec.t_Vec Golden_dkg.Threshold.Types.t_KeyShare Alloc.Alloc.t_Global &
      Golden_dkg.Threshold.Types.t_GroupInfo) =
  Rust_primitives.Hax.failure "The bindings [\"rng\"] cannot be mutated here: they don't belong to the closure scope, and this is not allowed.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/1060.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `LocalMutation`.\n"
    "{\n let mut rng: rand_core::os::t_OsRng = { rand_core::os::OsRng() };\n {\n let Tuple2(\n tmp0,\n out,\n ): tuple2<\n rand_core::os::t_OsRng,\n ark_ff::fields::models::fp::t_Fp<\n ark_ff::fields::models::fp::m..."
