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
Require Import pop_heap.Axiomatic.Axiomatic.
Require Import pop_heap.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import pop_heap.A_Count.A_Count.
Open Scope Z_scope.
Definition p_heapmaximumchild (mint_0 : addr -> Z) (a : addr) (n : Z) (p : Z) (c : Z) := let x : Z := l_heapleft p in let x_1 : Z := mint_0 (shift a c) in let x_2 : Z := l_heapright p in 0%Z ≤ p ∧ 2%Z + p ≤ n ∧ (p ≤ 2147483646%Z -> l_heapparent c = p) ∧ (2%Z + x ≤ n -> mint_0 (shift a x) ≤ x_1) ∧ (2%Z + x_2 ≤ n -> mint_0 (shift a x_2) ≤ x_1).
Definition p_multisetunchanged_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) := ∀(i : Z), is_sint32 i -> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i.
