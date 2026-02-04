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
Require Import contiki_memb.Compound.Compound.
Require Import contiki_memb.A_OccArray.A_OccArray.
Open Scope Z_scope.
Definition p_valid_memb (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (m : addr) := let x : Z := mint_0 (shift m 0%Z) in let x_1 : Z := mint_0 (shift m 1%Z) in let x_2 : Z := x_1 * x in let a : addr := mptr_0 (shift m 2%Z) in let a_1 : addr := mptr_0 (shift m 3%Z) in let a_2 : addr := shift a 0%Z in let a_3 : addr := shift a_1 0%Z in 0%Z < x ∧ x_2 ≤ 2147483647%Z ∧ valid_rw malloc_0 m 4%Z ∧ valid_rw malloc_0 a 1%Z ∧ valid_rw malloc_0 a_1 1%Z ∧ valid_rw malloc_0 a_2 x_1 ∧ valid_rw malloc_0 a_3 x_2 ∧ separated a_2 x_1 a_3 x_2.
Definition p__memb_full (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (mint_0 : addr -> Z) (m : addr) := ∀(i : Z), 0%Z ≤ i -> i < mint_0 (shift m 1%Z) -> ¬ mchar_0 (shift (mptr_0 (shift m 2%Z)) i) = 0%Z.
Definition l__memb_index (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (m : addr) (ptr_0 : addr) : Z := Z.rem (offset ptr_0 - offset (mptr_0 (shift m 3%Z))) (mint_0 (shift m 0%Z)).
Definition l__memb_ptr (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (m : addr) (index_0 : Z) : addr := shift (mptr_0 (shift m 3%Z)) (index_0 * mint_0 (shift m 0%Z)).
Definition p__memb_has (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (m : addr) (ptr_0 : addr) := ∃(i : Z), l__memb_ptr mptr_0 mint_0 m i = ptr_0 ∧ 0%Z ≤ i ∧ i < mint_0 (shift m 1%Z).
Definition p__memb_allocated (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (mint_0 : addr -> Z) (m : addr) (ptr_0 : addr) := ¬ mchar_0 (shift (mptr_0 (shift m 2%Z)) (l__memb_index mptr_0 mint_0 m ptr_0)) = 0%Z ∧ p__memb_has mptr_0 mint_0 m ptr_0.
Definition l__memb_numfree (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (mint_0 : addr -> Z) (m : addr) : Z := l_occ_a mchar_0 0%Z (mptr_0 (shift m 2%Z)) 0%Z (mint_0 (shift m 1%Z)).
Definition p__memb_empty (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (mint_0 : addr -> Z) (m : addr) := ∀(i : Z), 0%Z ≤ i -> i < mint_0 (shift m 1%Z) -> mchar_0 (shift (mptr_0 (shift m 2%Z)) i) = 0%Z.
Axiom Q_mult_simplification : forall  (b : Z) (a : Z) (fact0 : 0%Z < b) (fact1 : 0%Z ≤ a), Z.rem (a * b) b = a.
