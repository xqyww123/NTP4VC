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
Inductive s10_realrmat_s :=
  | s10_realrmat_s'mk : R -> R -> R -> R -> R -> R -> R -> R -> R -> s10_realrmat_s.
Axiom s10_realrmat_s_inhabited : Inhabited s10_realrmat_s.
Global Existing Instance s10_realrmat_s_inhabited.
Axiom s10_realrmat_s_countable : Countable s10_realrmat_s.
Global Existing Instance s10_realrmat_s_countable.
Definition f10_realrmat_s_a00 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk a _ _ _ _ _ _ _ _ => a end.
Definition f10_realrmat_s_a01 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ a _ _ _ _ _ _ _ => a end.
Definition f10_realrmat_s_a02 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ a _ _ _ _ _ _ => a end.
Definition f10_realrmat_s_a10 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ a _ _ _ _ _ => a end.
Definition f10_realrmat_s_a11 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ _ a _ _ _ _ => a end.
Definition f10_realrmat_s_a12 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ _ _ a _ _ _ => a end.
Definition f10_realrmat_s_a20 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ _ _ _ a _ _ => a end.
Definition f10_realrmat_s_a21 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ _ _ _ _ a _ => a end.
Definition f10_realrmat_s_a22 (x : s10_realrmat_s) := match x with |  s10_realrmat_s'mk _ _ _ _ _ _ _ _ a => a end.
Definition eqs10_realrmat_s (s : s10_realrmat_s) (s_1 : s10_realrmat_s) := f10_realrmat_s_a00 s_1 = f10_realrmat_s_a00 s ∧ f10_realrmat_s_a01 s_1 = f10_realrmat_s_a01 s ∧ f10_realrmat_s_a02 s_1 = f10_realrmat_s_a02 s ∧ f10_realrmat_s_a10 s_1 = f10_realrmat_s_a10 s ∧ f10_realrmat_s_a11 s_1 = f10_realrmat_s_a11 s ∧ f10_realrmat_s_a12 s_1 = f10_realrmat_s_a12 s ∧ f10_realrmat_s_a20 s_1 = f10_realrmat_s_a20 s ∧ f10_realrmat_s_a21 s_1 = f10_realrmat_s_a21 s ∧ f10_realrmat_s_a22 s_1 = f10_realrmat_s_a22 s.
