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
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Definition p_valid_strn (malloc_0 : Z -> Z) (mchar_0 : addr -> Z) (s : addr) (cnt_0 : Z) := let a : addr := shift s 0%Z in valid_rw malloc_0 a (1%Z + cnt_0) ∨ (∃(i : Z), mchar_0 (shift s i) = 0%Z ∧ i < cnt_0 ∧ is_uint64 i ∧ valid_rw malloc_0 a (1%Z + i)) ∧ (∀(j : Z), j ≤ cnt_0 -> is_sint8 (mchar_0 (shift s j))).
Axiom l_strnlen : (addr -> Z) -> addr -> Z -> Z.
Axiom fix_l_strnlen : forall  (mchar_0 : addr -> Z) (s : addr) (cnt_0 : Z), if decide (cnt_0 = 0%Z ∨ mchar_0 (shift s 0%Z) = 0%Z) then l_strnlen mchar_0 s cnt_0 = 0%Z else to_uint64 (1%Z + l_strnlen mchar_0 (shift s 1%Z) (to_uint64 (cnt_0 - 1%Z))) = l_strnlen mchar_0 s cnt_0.
Axiom Q_TL_strnlen : forall  (mchar_0 : addr -> Z) (s : addr) (cnt_0 : Z), is_uint64 (l_strnlen mchar_0 s cnt_0).
