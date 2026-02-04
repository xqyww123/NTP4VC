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
Require Import equal_range.Compound.Compound.
Open Scope Z_scope.
Definition p_strictlowerbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> v < mint_0 (shift a i).
Definition p_constantrange (mint_0 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) (val_0 : Z) := ∀(i : Z), first_0 ≤ i -> i < last_0 -> mint_0 (shift a i) = val_0.
Definition p_strictupperbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> mint_0 (shift a i) < v.
Definition p_sorted_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) := ∀(i_1 : Z) (i : Z), i < n -> m ≤ i_1 -> i_1 < i -> mint_0 (shift a i_1) ≤ mint_0 (shift a i).
Definition p_upperbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> mint_0 (shift a i) ≤ v.
Definition p_lowerbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> v ≤ mint_0 (shift a i).
