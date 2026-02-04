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
Require Import Why3.Memory.Memory.
Open Scope Z_scope.
Inductive s1_list :=
  | s1_list'mk : addr -> R -> R -> R -> s1_list.
Axiom s1_list_inhabited : Inhabited s1_list.
Global Existing Instance s1_list_inhabited.
Axiom s1_list_countable : Countable s1_list.
Global Existing Instance s1_list_countable.
Definition f1_list_next (x : s1_list) := match x with |  s1_list'mk a _ _ _ => a end.
Definition f1_list_x (x : s1_list) := match x with |  s1_list'mk _ a _ _ => a end.
Definition f1_list_y (x : s1_list) := match x with |  s1_list'mk _ _ a _ => a end.
Definition f1_list_z (x : s1_list) := match x with |  s1_list'mk _ _ _ a => a end.
Definition eqs1_list (s : s1_list) (s_1 : s1_list) := f1_list_next s_1 = f1_list_next s ∧ f1_list_x s_1 = f1_list_x s ∧ f1_list_y s_1 = f1_list_y s ∧ f1_list_z s_1 = f1_list_z s.
