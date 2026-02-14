module Libspartan

assume new type t_Instance (f : Type0) : Type0
assume new type t_Assignment (f : Type0) : Type0

assume val impl_1__new : #f:Type0 -> #a:Type0 -> a -> a -> a -> t_Instance f
assume val impl__new : #f:Type0 -> #a:Type0 -> a -> t_Assignment f
