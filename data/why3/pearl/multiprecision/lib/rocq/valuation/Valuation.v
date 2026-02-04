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
Axiom valuation : Z -> Z -> Z.
Axiom valuation'def : forall  (p : Z) (n : Z) (fact0 : 1%Z < p) (fact1 : 1%Z ≤ n), if decide (Z.quot n p = 0%Z) then valuation n p = valuation (Z.rem n p) p + 1%Z else valuation n p = 0%Z.
Axiom valuation'spec'0 : forall  (p : Z) (n : Z) (fact0 : 1%Z < p) (fact1 : 1%Z ≤ n), 0%Z ≤ valuation n p.
Axiom valuation'spec : forall  (p : Z) (n : Z) (fact0 : 1%Z < p) (fact1 : 1%Z ≤ n), (Z.pow p (valuation n p) | n).
