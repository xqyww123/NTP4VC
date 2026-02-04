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
Require Import remove_copy.A_Count.A_Count.
Require Import Why3.Cint.Cint.
Require Import remove_copy.Compound.Compound.
Require Import remove_copy.Axiomatic.Axiomatic.
Open Scope Z_scope.
Definition p_multisetretainrest_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (m1_0 : Z) (m2_0 : Z) (b : addr) (n1_0 : Z) (n2_0 : Z) (v : Z) := ∀(i : Z), ¬ i = v -> is_sint32 i -> l_count_1' mint_1 a m1_0 m2_0 i = l_count_1' mint_0 b n1_0 n2_0 i.
