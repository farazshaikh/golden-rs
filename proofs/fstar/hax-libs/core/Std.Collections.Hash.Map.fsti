module Std.Collections.Hash.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val t_HashMap (v_K v_V v_S: Type0) : eqtype

/// Iterator types returned by HashMap methods.
val t_Iter (v_K: Type0) (v_V: Type0) : Type0
val t_Keys (v_K: Type0) (v_V: Type0) (v_S: Type0) : Type0
val t_Values (v_K: Type0) (v_V: Type0) (v_S: Type0) : Type0
val t_IntoIter (v_K: Type0) (v_V: Type0) (v_S: Type0) : Type0

val impl__new: #v_K: Type0 -> #v_V: Type0 -> Prims.unit
  -> Prims.Pure (t_HashMap v_K v_V Std.Hash.Random.t_RandomState)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// HashMap::len()
val impl_1__len (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// HashMap::iter() -> Iter<K, V>
val impl_1__iter (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S)
    : Prims.Pure (t_Iter v_K v_V) Prims.l_True (fun _ -> Prims.l_True)

/// HashMap::keys() -> Keys<K, V, S>
val impl_1__keys (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S)
    : Prims.Pure (t_Keys v_K v_V v_S) Prims.l_True (fun _ -> Prims.l_True)

/// HashMap::values() -> Values<K, V, S>
val impl_1__values (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S)
    : Prims.Pure (t_Values v_K v_V v_S) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__get (#v_K #v_V #v_S #v_Y: Type0) (m: t_HashMap v_K v_V v_S) (k: v_K)
    : Prims.Pure (Core_models.Option.t_Option v_V) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__insert (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S) (k: v_K) (v: v_V)
    : Prims.Pure (t_HashMap v_K v_V v_S & Core_models.Option.t_Option v_V)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// HashMap::contains_key()
val impl_2__contains_key (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S) (k: v_K)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
