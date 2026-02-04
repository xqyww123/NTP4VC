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
Require Import stack_top_wd.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Definition l_storage (mptr_0 : addr -> addr) (s : addr) : addr := mptr_0 (shift s 0%Z).
Definition l_capacity (mint_0 : addr -> Z) (s : addr) : Z := mint_0 (shift s 1%Z).
Definition l_size (mint_0 : addr -> Z) (s : addr) : Z := mint_0 (shift s 2%Z).
Definition p_invariant (malloc_0 : Z -> Z) (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (s : addr) := let x : Z := l_capacity mint_0 s in let x_1 : Z := l_size mint_0 s in let a : addr := shift (l_storage mptr_0 s) 0%Z in 0%Z < x ∧ x_1 ≤ x ∧ 0%Z ≤ x_1 ∧ valid_rw malloc_0 a x ∧ separated s 3%Z a x.
Definition l_top (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (s : addr) : Z := mint_0 (shift (mptr_0 (shift s 0%Z)) (mint_0 (shift s 2%Z) - 1%Z)).
Definition p_empty (mint_0 : addr -> Z) (s : addr) := l_size mint_0 s = 0%Z.
Definition p_equalranges_1' (mint_0 : addr -> Z) (mint_1 : addr -> Z) (a : addr) (n : Z) (b : addr) := ∀(i : Z), 0%Z ≤ i -> i < n -> mint_1 (shift a i) = mint_0 (shift b i).
Definition p_equal (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (mptr_1 : addr -> addr) (mint_1 : addr -> Z) (s : addr) (t : addr) := let x : Z := l_size mint_1 s in l_size mint_0 t = x ∧ p_equalranges_1' mint_0 mint_1 (l_storage mptr_1 s) x (l_storage mptr_0 t).
Axiom Q_TL_Capacity : forall  (mint_0 : addr -> Z) (s : addr), is_uint32 (l_capacity mint_0 s).
Axiom Q_TL_Size : forall  (mint_0 : addr -> Z) (s : addr), is_uint32 (l_size mint_0 s).
Axiom Q_TL_Top : forall  (mptr_0 : addr -> addr) (mint_0 : addr -> Z) (s : addr), is_sint32 (l_top mptr_0 mint_0 s).
