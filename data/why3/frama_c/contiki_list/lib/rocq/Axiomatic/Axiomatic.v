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
Inductive p_linked_n : (Z -> Z) -> (addr -> addr) -> addr -> addr -> Z -> Z -> addr -> Prop :=
 | Q_linked_n_bound (index_0 : Z) (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (bound_0 : addr) (array_0 : addr) : 0%Z ≤ index_0 -> index_0 ≤ 2147483646%Z -> p_linked_n malloc_0 mptr_0 bound_0 array_0 index_0 0%Z bound_0
 | Q_linked_n_cons (index_0 : Z) (n : Z) (mptr_0 : addr -> addr) (array_0 : addr) (root_0 : addr) (malloc_0 : Z -> Z) (bound_0 : addr) : (let x : Z := index_0 + n in mptr_0 (shift array_0 index_0) = root_0 -> 0%Z < n -> 0%Z ≤ index_0 -> 0%Z ≤ x -> x ≤ 2147483646%Z -> valid_rw malloc_0 root_0 4%Z -> p_linked_n malloc_0 mptr_0 (mptr_0 (shift root_0 0%Z)) array_0 (1%Z + index_0) (n - 1%Z) bound_0 -> p_linked_n malloc_0 mptr_0 root_0 array_0 index_0 n bound_0).
