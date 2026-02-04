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
Inductive s5_floatrmat :=
  | s5_floatrmat'mk : (Z -> R) -> s5_floatrmat.
Axiom s5_floatrmat_inhabited : Inhabited s5_floatrmat.
Global Existing Instance s5_floatrmat_inhabited.
Axiom s5_floatrmat_countable : Countable s5_floatrmat.
Global Existing Instance s5_floatrmat_countable.
Definition f5_floatrmat_m (x : s5_floatrmat) := match x with |  s5_floatrmat'mk a => a end.
