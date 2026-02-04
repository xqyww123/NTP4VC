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
Require Import contiki_list.Compound.Compound.
Require Import contiki_list.S1_list.S1_list.
Open Scope Z_scope.
Definition p_unchanged (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (mflt_0 : addr -> R) (malloc_1 : Z -> Z) (mptr_1 : addr -> addr) (mflt_1 : addr -> R) (array_0 : addr) (down_0 : Z) (up_0 : Z) := ∀(i : Z), let a : addr := shift array_0 i in let a_1 : addr := mptr_0 a in let a_2 : addr := mptr_1 a in down_0 ≤ i -> i < up_0 -> a_1 = a_2 ∧ eqs1_list (load_s1_list a_2 mflt_1 mptr_1) (load_s1_list a_1 mflt_0 mptr_0) ∧ (valid_rw malloc_1 a_2 4%Z -> valid_rw malloc_0 a_1 4%Z).
Definition p_array_swipe_left (mptr_0 : addr -> addr) (mptr_1 : addr -> addr) (array_0 : addr) (down_0 : Z) (up_0 : Z) := ∀(i : Z), down_0 ≤ i -> i < up_0 -> mptr_1 (shift array_0 (1%Z + i)) = mptr_0 (shift array_0 i).
Definition p_array_swipe_right (mptr_0 : addr -> addr) (mptr_1 : addr -> addr) (array_0 : addr) (down_0 : Z) (up_0 : Z) := ∀(i : Z), down_0 ≤ i -> i < up_0 -> mptr_1 (shift array_0 (i - 1%Z)) = mptr_0 (shift array_0 i).
