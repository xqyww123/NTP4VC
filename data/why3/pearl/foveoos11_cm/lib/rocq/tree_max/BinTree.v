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
Open Scope Z_scope.
Inductive tree :=
  | Null : tree
  | Tree : Z -> tree -> tree -> tree.
Axiom tree_inhabited : Inhabited tree.
Global Existing Instance tree_inhabited.
Axiom tree_countable : Countable tree.
Global Existing Instance tree_countable.
Program Fixpoint mem (v : Z) (t : tree) : Prop :=
match t with | Null => False | Tree x l r => x = v ∨ mem v l ∨ mem v r end.
Admit Obligations.
Program Fixpoint ge_tree (v : Z) (t : tree) : Prop :=
match t with | Null => True | Tree x l r => x ≤ v ∧ ge_tree v l ∧ ge_tree v r end.
Admit Obligations.
