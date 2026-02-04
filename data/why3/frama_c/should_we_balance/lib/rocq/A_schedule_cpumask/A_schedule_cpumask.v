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
Require Import should_we_balance.Compound.Compound.
Require Import should_we_balance.A_thread_variables_properties.A_thread_variables_properties.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Axiom l_idle_cpu : Z -> Z.
Axiom l_sched_group_cpus : addr -> addr.
Axiom l_sched_group_mask : addr -> addr.
Axiom l_group_balance_mask : addr -> addr.
Axiom l_group_balance_cpu : addr -> Z.
Axiom l_cpu_smt_mask : Z -> addr.
Definition p_idle_core (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (cpu_0 : Z) := ∀(i : Z), ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask cpu_0) 0%Z)) i) = 0%Z -> 0%Z ≤ i -> i < l_size -> ¬ l_idle_cpu i = 0%Z.
Axiom Q_TL_idle_cpu : forall  (cpu_0 : Z), is_uint8 (l_idle_cpu cpu_0).
Axiom Q_mask_refl : forall  (i : Z) (mint_0 : addr -> Z) (mptr_0 : addr -> addr) (fact0 : 0%Z ≤ i) (fact1 : i < l_size), ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask i) 0%Z)) i) = 0%Z.
Axiom Q_mask_symm : forall  (mint_0 : addr -> Z) (mptr_0 : addr -> addr) (j : Z) (i : Z) (fact0 : ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask j) 0%Z)) i) = 0%Z) (fact1 : 0%Z ≤ i) (fact2 : i < l_size) (fact3 : 0%Z ≤ j) (fact4 : j < l_size), ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask i) 0%Z)) j) = 0%Z.
Axiom Q_mask_trans : forall  (mptr_0 : addr -> addr) (i : Z) (mint_0 : addr -> Z) (j : Z) (k : Z), ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask i) 0%Z)) j) = 0%Z -> ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask j) 0%Z)) k) = 0%Z -> 0%Z ≤ i -> i < l_size -> 0%Z ≤ j -> j < l_size -> 0%Z ≤ k -> k < l_size -> ¬ mint_0 (shift (mptr_0 (shift (l_cpu_smt_mask i) 0%Z)) k) = 0%Z.
