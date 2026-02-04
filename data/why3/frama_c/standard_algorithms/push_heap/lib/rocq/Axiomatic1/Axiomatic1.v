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
Require Import push_heap.A_Count.A_Count.
Require Import Why3.Cint.Cint.
Require Import push_heap.Compound.Compound.
Require Import push_heap.Axiomatic.Axiomatic.
Open Scope Z_scope.
Definition p_multisetadd (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (val_0 : Z) := 1%Z + l_count_1' mint_1 a 0%Z n val_0 = l_count_1' mint_0 a 0%Z n val_0.
Definition p_multisetminus (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (val_0 : Z) := 1%Z + l_count_1' mint_0 a 0%Z n val_0 = l_count_1' mint_1 a 0%Z n val_0.
Definition p_multisetretain (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (v : Z) := l_count_1' mint_1 a 0%Z n v = l_count_1' mint_0 a 0%Z n v.
Definition p_multisetretainrest_3' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (v : Z) (w : Z) := ∀(i : Z), ¬ i = v -> ¬ i = w -> is_sint32 i -> p_multisetretain mint_0 mint_1 a n i.
Definition p_multisetunchanged_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (first_0 : Z) (last_0 : Z) := ∀(i : Z), is_sint32 i -> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i.
