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
Require Import klibc_stdio.Compound.Compound.
Open Scope Z_scope.
Definition p_valid_file (malloc_0 : Z -> Z) (mint_0 : addr -> Z) (f : addr) := 0%Z ≤ mint_0 (shift f 0%Z) ∧ valid_rw malloc_0 f 3%Z.
Definition p_valid_io_file_pvt_norec (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (f : addr) := let x : Z := mint_0 (shift f 9%Z) in let x_1 : Z := mint_0 (shift f 7%Z) in let x_2 : Z := mint_0 (shift f 8%Z) in let a : addr := mptr_0 (shift f 5%Z) in let a_1 : addr := mptr_0 (shift f 6%Z) in let a_2 : addr := mptr_0 (shift f 4%Z) in let a_3 : addr := mptr_0 (shift f 3%Z) in let a_4 : addr := shift a 0%Z in let x_3 : Z := 32%Z + x in x = 16384%Z ∧ 0%Z ≤ x_1 ∧ x_1 < x ∧ 0%Z ≤ x_2 ∧ x_2 < x ∧ valid_rw malloc_0 f 11%Z ∧ addr_le a a_1 ∧ p_valid_file malloc_0 mint_0 (shift f 0%Z) ∧ valid_rw malloc_0 a_2 11%Z ∧ valid_rw malloc_0 a_3 11%Z ∧ separated f 11%Z a_2 11%Z ∧ separated f 11%Z a_3 11%Z ∧ separated a_2 11%Z a_3 11%Z ∧ valid_rw malloc_0 a_4 x_3 ∧ separated f 11%Z a_4 x_3 ∧ separated a_2 11%Z a_4 x_3 ∧ separated a_3 11%Z a_4 x_3 ∧ addr_lt a_1 (shift a x_3).
Definition p_valid_io_file_pvt (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (f : addr) := let x : Z := mint_0 (shift f 9%Z) in let a : addr := mptr_0 (shift f 6%Z) in let a_1 : addr := mptr_0 (shift f 5%Z) in let a_2 : addr := mptr_0 (shift f 3%Z) in let a_3 : addr := mptr_0 (shift f 4%Z) in let x_1 : Z := mint_0 (shift f 7%Z) in let x_2 : Z := mint_0 (shift f 8%Z) in let a_4 : addr := shift a_1 0%Z in let x_3 : Z := 32%Z + x in x = 16384%Z ∧ base a = base a_1 ∧ mptr_0 (shift a_2 4%Z) = f ∧ mptr_0 (shift a_3 3%Z) = f ∧ 0%Z ≤ x_1 ∧ x_1 < x ∧ 0%Z ≤ x_2 ∧ x_2 < x ∧ valid_rw malloc_0 f 11%Z ∧ addr_le a_1 a ∧ p_valid_file malloc_0 mint_0 (shift f 0%Z) ∧ separated f 11%Z a_3 11%Z ∧ separated f 11%Z a_2 11%Z ∧ separated a_3 11%Z a_2 11%Z ∧ p_valid_io_file_pvt_norec malloc_0 mptr_0 mint_0 a_3 ∧ p_valid_io_file_pvt_norec malloc_0 mptr_0 mint_0 a_2 ∧ valid_rw malloc_0 a_4 x_3 ∧ separated f 11%Z a_4 x_3 ∧ separated a_3 11%Z a_4 x_3 ∧ separated a_2 11%Z a_4 x_3 ∧ addr_lt a (shift a_1 x_3).
