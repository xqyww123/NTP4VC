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
Require Import verker.A_StrSpn.A_StrSpn.
Require Import verker.Compound.Compound.
Require Import verker.A_Strlen.A_Strlen.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Axiom l_strcspn : addr -> addr -> Z.
Axiom Q_strcspn_base_case : forall  (mchar_0 : addr -> Z) (s : addr) (reject_0 : addr) (fact0 : mchar_0 s = 0%Z), l_strcspn s reject_0 = 0%Z.
Axiom Q_strcspn_in_reject : forall  (mchar_0 : addr -> Z) (s : addr) (reject_0 : addr), ¬ mchar_0 s = 0%Z -> p_in_array mchar_0 reject_0 (mchar_0 s) -> l_strcspn s reject_0 = 0%Z.
Axiom Q_strcspn_not_in_reject : forall  (mchar_0 : addr -> Z) (s : addr) (reject_0 : addr), ¬ mchar_0 s = 0%Z -> ¬ p_in_array mchar_0 reject_0 (mchar_0 s) -> 1%Z + l_strcspn (shift s 1%Z) reject_0 = l_strcspn s reject_0.
