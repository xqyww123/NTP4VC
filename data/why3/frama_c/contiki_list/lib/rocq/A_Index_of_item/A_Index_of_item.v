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
Axiom l_index_of : (addr -> addr) -> addr -> addr -> Z -> Z -> Z.
Axiom Q_no_more_elements : forall  (up_0 : Z) (down_0 : Z) (mptr_0 : addr -> addr) (item_0 : addr) (array_0 : addr) (fact0 : up_0 ≤ down_0) (fact1 : 0%Z ≤ up_0), l_index_of mptr_0 item_0 array_0 down_0 up_0 = up_0.
Axiom Q_found_item : forall  (mptr_0 : addr -> addr) (array_0 : addr) (down_0 : Z) (item_0 : addr) (up_0 : Z) (fact0 : mptr_0 (shift array_0 down_0) = item_0) (fact1 : 0%Z ≤ down_0) (fact2 : down_0 < up_0), l_index_of mptr_0 item_0 array_0 down_0 up_0 = down_0.
Axiom Q_not_the_item : forall  (mptr_0 : addr -> addr) (array_0 : addr) (down_0 : Z) (item_0 : addr) (up_0 : Z) (fact0 : ¬ mptr_0 (shift array_0 down_0) = item_0) (fact1 : 0%Z ≤ down_0) (fact2 : down_0 < up_0), l_index_of mptr_0 item_0 array_0 (1%Z + down_0) up_0 = l_index_of mptr_0 item_0 array_0 down_0 up_0.
