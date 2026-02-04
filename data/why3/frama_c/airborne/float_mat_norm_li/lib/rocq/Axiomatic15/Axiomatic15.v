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
Require Import float_mat_norm_li.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Definition p_valid_size (n : Z) := 0%Z ≤ n ∧ n ≤ 2147483646%Z.
Definition p_rvalid_float_mat_2' (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (a : addr) (m : Z) (n : Z) := p_valid_size m ∧ p_valid_size n ∧ valid_rd malloc_0 (shift a 0%Z) m ∧ (∀(i : Z), 0%Z ≤ i -> i < m -> is_sint32 i -> valid_rd malloc_0 (shift (mptr_0 (shift a i)) 0%Z) n).
