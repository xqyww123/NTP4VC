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
Require Import search_n.Compound.Compound.
Open Scope Z_scope.
Definition p_constantrange (mint_0 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) (val_0 : Z) := ∀(i : Z), first_0 ≤ i -> i < last_0 -> mint_0 (shift a i) = val_0.
Definition p_hasconstantsubrange (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (b : Z) := ∃(i : Z), let x : Z := n + i in 0%Z ≤ i ∧ x ≤ m ∧ p_constantrange mint_0 a i x b.
