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
Require Import int32_quat_of_rmat.Compound.Compound.
Open Scope Z_scope.
Definition p_bound_int32rmat (mint_0 : addr -> Z) (rm_0 : addr) (bound_0 : Z) := let a : addr := shift rm_0 0%Z in let x : Z := mint_0 (shift a 0%Z) in let x_1 : Z := mint_0 (shift a 1%Z) in let x_2 : Z := mint_0 (shift a 2%Z) in let x_3 : Z := mint_0 (shift a 3%Z) in let x_4 : Z := mint_0 (shift a 4%Z) in let x_5 : Z := mint_0 (shift a 5%Z) in let x_6 : Z := mint_0 (shift a 6%Z) in let x_7 : Z := mint_0 (shift a 7%Z) in let x_8 : Z := mint_0 (shift a 8%Z) in x ≤ bound_0 ∧ x_1 ≤ bound_0 ∧ x_2 ≤ bound_0 ∧ x_3 ≤ bound_0 ∧ x_4 ≤ bound_0 ∧ x_5 ≤ bound_0 ∧ x_6 ≤ bound_0 ∧ x_7 ≤ bound_0 ∧ x_8 ≤ bound_0 ∧ 0%Z ≤ bound_0 + x ∧ 0%Z ≤ bound_0 + x_1 ∧ 0%Z ≤ bound_0 + x_2 ∧ 0%Z ≤ bound_0 + x_3 ∧ 0%Z ≤ bound_0 + x_4 ∧ 0%Z ≤ bound_0 + x_5 ∧ 0%Z ≤ bound_0 + x_6 ∧ 0%Z ≤ bound_0 + x_7 ∧ 0%Z ≤ bound_0 + x_8.
Definition p_rvalid_bound_int32rmat (malloc_0 : Z -> Z) (mint_0 : addr -> Z) (rm_0 : addr) (bound_0 : Z) := valid_rd malloc_0 rm_0 9%Z ∧ p_bound_int32rmat mint_0 rm_0 bound_0.
