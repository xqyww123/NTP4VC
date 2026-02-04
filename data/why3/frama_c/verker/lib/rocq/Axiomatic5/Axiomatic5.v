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
Open Scope Z_scope.
Definition p_kstrtobool_fmt_false (mchar_0 : addr -> Z) (s : addr) := let x : Z := mchar_0 (shift s 0%Z) in let x_1 : Z := mchar_0 (shift s 1%Z) in x = 48%Z ∨ x = 78%Z ∨ x = 110%Z ∨ (x = 79%Z ∨ x = 111%Z) ∧ (x_1 = 70%Z ∨ x_1 = 102%Z).
Definition p_kstrtobool_fmt_true (mchar_0 : addr -> Z) (s : addr) := let x : Z := mchar_0 (shift s 0%Z) in let x_1 : Z := mchar_0 (shift s 1%Z) in x = 49%Z ∨ x = 89%Z ∨ x = 121%Z ∨ (x = 79%Z ∨ x = 111%Z) ∧ (x_1 = 78%Z ∨ x_1 = 110%Z).
Definition p_kstrtobool_fmt (mchar_0 : addr -> Z) (s : addr) := p_kstrtobool_fmt_false mchar_0 s ∨ p_kstrtobool_fmt_true mchar_0 s.
