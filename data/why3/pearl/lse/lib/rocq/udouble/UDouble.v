From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.ieee_float.RoundingMode.
Open Scope Z_scope.
Axiom udouble : Type.
Axiom udouble_inhabited : Inhabited udouble.
Global Existing Instance udouble_inhabited.
Axiom udouble_countable : Countable udouble.
Global Existing Instance udouble_countable.
Axiom to_real : udouble -> R.
Axiom uround : mode -> R -> udouble.
Axiom uround_exact : forall  (m : mode) (x : udouble), uround m (to_real x) = x.
Axiom uzero : udouble.
Axiom to_real_uzero : to_real uzero = 0%R.
Axiom utwo : udouble.
Axiom to_real_utwo : to_real utwo = 2%R.
Definition uadd (x : udouble) (y : udouble) : udouble := uround RNE (Rplus (to_real x) (to_real y)).
Definition usub (x : udouble) (y : udouble) : udouble := uround RNE (Rminus (to_real x) (to_real y)).
Definition umul (x : udouble) (y : udouble) : udouble := uround RNE (Rmult (to_real x) (to_real y)).
Definition udiv (x : udouble) (y : udouble) : udouble := uround RNE (Rdiv (to_real x) (to_real y)).
Definition uminus (x : udouble) : udouble := uround RNE (Ropp (to_real x)).
