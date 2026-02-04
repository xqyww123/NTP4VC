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
Require Import verker.A_Ctype.A_Ctype.
Open Scope Z_scope.
Definition p_is_hex (mchar_0 : addr -> Z) (s : addr) := mchar_0 (shift s 0%Z) = 48%Z ∧ l_tolower (mchar_0 (shift s 1%Z)) = 120%Z ∧ p_isxdigit (mchar_0 (shift s 2%Z)).
Definition p_is_oct (mchar_0 : addr -> Z) (s : addr) := mchar_0 (shift s 0%Z) = 48%Z ∧ ¬ p_is_hex mchar_0 s.
Definition p_is_dec (mchar_0 : addr -> Z) (s : addr) := ¬ p_is_hex mchar_0 s ∧ ¬ p_is_oct mchar_0 s.
