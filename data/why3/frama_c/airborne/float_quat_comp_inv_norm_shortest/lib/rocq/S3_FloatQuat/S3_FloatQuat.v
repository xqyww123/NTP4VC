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
Inductive s3_floatquat :=
  | s3_floatquat'mk : R -> R -> R -> R -> s3_floatquat.
Axiom s3_floatquat_inhabited : Inhabited s3_floatquat.
Global Existing Instance s3_floatquat_inhabited.
Axiom s3_floatquat_countable : Countable s3_floatquat.
Global Existing Instance s3_floatquat_countable.
Definition f3_floatquat_qi (x : s3_floatquat) := match x with |  s3_floatquat'mk a _ _ _ => a end.
Definition f3_floatquat_qx (x : s3_floatquat) := match x with |  s3_floatquat'mk _ a _ _ => a end.
Definition f3_floatquat_qy (x : s3_floatquat) := match x with |  s3_floatquat'mk _ _ a _ => a end.
Definition f3_floatquat_qz (x : s3_floatquat) := match x with |  s3_floatquat'mk _ _ _ a => a end.
