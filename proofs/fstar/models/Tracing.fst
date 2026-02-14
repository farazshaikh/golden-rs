module Tracing

/// Tracing crate stub.
/// __macro_support is modeled as a record value because F* doesn't
/// allow `__` in module names (Tracing.__macro_support can't be a module).
/// Access pattern: Tracing.__macro_support.e_ee_is_enabled x y

module Level_filters = Tracing.Level_filters

noeq type __macro_support_rec = {
  e_ee_is_enabled : #v_A:Type0 -> #v_B:Type0 -> v_A -> v_B -> bool;
}

assume val __macro_support : __macro_support_rec
