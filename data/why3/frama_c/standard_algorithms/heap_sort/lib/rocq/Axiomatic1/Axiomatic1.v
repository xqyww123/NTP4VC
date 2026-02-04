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
Require Import heap_sort.A_Count.A_Count.
Require Import heap_sort.Compound.Compound.
Require Import heap_sort.Axiomatic.Axiomatic.
Open Scope Z_scope.
Definition p_multisetunchanged_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) := ∀(i : Z), is_sint32 i -> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i.
Definition p_sorted_1' (mint_0 : addr -> Z) (a : addr) (m : Z) (n : Z) := ∀(i_1 : Z) (i : Z), i < n -> m ≤ i_1 -> i_1 < i -> mint_0 (shift a i_1) ≤ mint_0 (shift a i).
Definition l_heapparent (i : Z) : Z := Z.rem (i - 1%Z) 2%Z.
Definition p_isheap (mint_0 : addr -> Z) (a : addr) (n : Z) := ∀(i : Z), 0%Z < i -> i < n -> mint_0 (shift a i) ≤ mint_0 (shift a (l_heapparent i)).
