module Num_traits.Identities

/// Zero/One traits. The extraction calls these with a tcresolve parameter:
///   f_zero #Type #FStar.Tactics.Typeclasses.solve ()
class t_Zero (v_Self : Type0) = { __zero_val : v_Self; }
class t_One (v_Self : Type0) = { __one_val : v_Self; }

assume val f_zero : #t:Type0 -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst:t_Zero t -> unit -> t
assume val f_is_zero : #t:Type0 -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst:t_Zero t -> t -> bool
assume val f_one : #t:Type0 -> #[FStar.Tactics.Typeclasses.tcresolve ()] _inst:t_One t -> unit -> t

/// Blanket instances for field elements
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_zero_fp (config : Type0) (n : Rust_primitives.Integers.usize) : t_Zero (t_Fp (t_MontBackend config n) n)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_one_fp (config : Type0) (n : Rust_primitives.Integers.usize) : t_One (t_Fp (t_MontBackend config n) n)
