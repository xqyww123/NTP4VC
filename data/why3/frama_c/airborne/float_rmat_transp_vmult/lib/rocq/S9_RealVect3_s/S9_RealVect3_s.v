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
Inductive s9_realvect3_s :=
  | s9_realvect3_s'mk : R -> R -> R -> s9_realvect3_s.
Axiom s9_realvect3_s_inhabited : Inhabited s9_realvect3_s.
Global Existing Instance s9_realvect3_s_inhabited.
Axiom s9_realvect3_s_countable : Countable s9_realvect3_s.
Global Existing Instance s9_realvect3_s_countable.
Definition f9_realvect3_s_x (x : s9_realvect3_s) := match x with |  s9_realvect3_s'mk a _ _ => a end.
Definition f9_realvect3_s_y (x : s9_realvect3_s) := match x with |  s9_realvect3_s'mk _ a _ => a end.
Definition f9_realvect3_s_z (x : s9_realvect3_s) := match x with |  s9_realvect3_s'mk _ _ a => a end.
Definition eqs9_realvect3_s (s : s9_realvect3_s) (s_1 : s9_realvect3_s) := f9_realvect3_s_x s_1 = f9_realvect3_s_x s ∧ f9_realvect3_s_y s_1 = f9_realvect3_s_y s ∧ f9_realvect3_s_z s_1 = f9_realvect3_s_z s.
