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
Require Import Why3.Cint.Cint.
Require Import partial_sum_inv.Compound.Compound.
Require Import partial_sum_inv.Axiomatic.Axiomatic.
Open Scope Z_scope.
Axiom l_difference : (addr -> Z) -> addr -> Z -> Z.
Axiom Q_TL_Difference : forall  (mint_0 : addr -> Z) (a : addr) (n : Z), is_sint32 (l_difference mint_0 a n).
Axiom Q_DifferenceEmptyOrSingle : forall  (n : Z) (mint_0 : addr -> Z) (a : addr) (fact0 : n ≤ 0%Z), mint_0 (shift a 0%Z) = l_difference mint_0 a n.
Axiom Q_DifferenceNext : forall  (n : Z) (mint_0 : addr -> Z) (a : addr) (fact0 : 0%Z < n), mint_0 (shift a n) = l_difference mint_0 a n + mint_0 (shift a (n - 1%Z)).
Axiom Q_DifferenceRead : forall  (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (fact0 : p_unchanged_1' mint_0 mint_1 a 0%Z (1%Z + n)), l_difference mint_1 a n = l_difference mint_0 a n.
