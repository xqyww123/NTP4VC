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
Require Import sort_heap.A_Count.A_Count.
Require Import Why3.Cint.Cint.
Require Import sort_heap.Compound.Compound.
Require Import sort_heap.Axiomatic.Axiomatic.
Open Scope Z_scope.
Definition p_upperbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> mint_0 (shift a i) ≤ v.
Definition p_maxelement (mint_0 : addr -> Z) (a : addr) (n : Z) (max_0 : Z) := 0%Z ≤ max_0 ∧ max_0 < n ∧ p_upperbound_1' mint_0 a 0%Z n (mint_0 (shift a max_0)).
Definition p_multisetunchanged_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) := ∀(i : Z), is_sint32 i -> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i.
Definition p_sorted_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) := ∀(i_1 : Z) (i : Z), i < n -> m ≤ i_1 -> i_1 < i -> mint_0 (shift a i_1) ≤ mint_0 (shift a i).
Definition p_lowerbound_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) (v : Z) := ∀(i : Z), m ≤ i -> i < n -> v ≤ mint_0 (shift a i).
