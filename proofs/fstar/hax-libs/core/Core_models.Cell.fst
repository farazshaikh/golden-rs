module Core_models.Cell
assume new type t_RefCell (t: Type0) : Type0
/// t_Ref: Rust's std::cell::Ref<T> takes only 1 type parameter.
/// The extraction uses t_Ref with 1 param (e.g., t_Ref (t_ConstraintSystem Fr)).
assume new type t_Ref (t1: Type0) : Type0
