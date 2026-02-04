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
Require Import Why3.Qed.Qed.
Open Scope Z_scope.
Inductive s8_int32quat :=
  | s8_int32quat'mk : Z -> Z -> Z -> Z -> s8_int32quat.
Axiom s8_int32quat_inhabited : Inhabited s8_int32quat.
Global Existing Instance s8_int32quat_inhabited.
Axiom s8_int32quat_countable : Countable s8_int32quat.
Global Existing Instance s8_int32quat_countable.
Definition f8_int32quat_qi (x : s8_int32quat) := match x with |  s8_int32quat'mk a _ _ _ => a end.
Definition f8_int32quat_qx (x : s8_int32quat) := match x with |  s8_int32quat'mk _ a _ _ => a end.
Definition f8_int32quat_qy (x : s8_int32quat) := match x with |  s8_int32quat'mk _ _ a _ => a end.
Definition f8_int32quat_qz (x : s8_int32quat) := match x with |  s8_int32quat'mk _ _ _ a => a end.
