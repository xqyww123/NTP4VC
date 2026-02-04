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
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Definition p_valid_str (malloc_0 : Z -> Z) (mchar_0 : addr -> Z) (s : addr) := ∃(i : Z), mchar_0 (shift s i) = 0%Z ∧ is_uint64 i ∧ valid_rw malloc_0 (shift s 0%Z) (1%Z + i) ∧ (∀(j : Z), j ≤ i -> is_sint8 (mchar_0 (shift s j))).
Axiom l_strlen : (addr -> Z) -> addr -> Z.
Axiom fix_l_strlen : forall  (mchar_0 : addr -> Z) (s : addr), if decide (mchar_0 (shift s 0%Z) = 0%Z) then l_strlen mchar_0 s = 0%Z else to_uint64 (1%Z + l_strlen mchar_0 (shift s 1%Z)) = l_strlen mchar_0 s.
Axiom Q_TL_strlen : forall  (mchar_0 : addr -> Z) (s : addr), is_uint64 (l_strlen mchar_0 s).
