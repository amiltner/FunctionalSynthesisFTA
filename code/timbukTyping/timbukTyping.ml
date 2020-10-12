(** Timbuk Typing

    This library provides several typing procedures:
    A Hindley–Milner polymorphic type inference algorithm,
    a monomorphisation algorithm,
    a sub-typing algorithm and
    the Regular Language Typing procedure for Higher-Order Functional TRS
    verification.
*)

(** {1 Hindley–Milner polymorphic type inference} *)

module PolyType = PolyType

module Poly = Poly

(** {1 Monomorphization} *)

module MonoType = MonoType

module Mono = Mono

(** {1 Sub-typing} *)

module Sub = Sub

(** {1 Regular type inference} *)

(** {2 Type system} *)

module RefinedTypeSystem = RefinedTypeSystem

(** {2 Inference} *)

module Regular = Regular

module Factorizer = Factorizer

(** {1 Utilities} *)

module LocType = LocType

(** {2 Higher-Order encoding} *)

module AppSymbol = AppSymbol
