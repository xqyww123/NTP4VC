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
Require Import verker.A_Strnlen.A_Strnlen.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Axiom l_strncmp_2' : (addr -> Z) -> addr -> addr -> Z -> Z.
Axiom fix_l_strncmp_2' : forall  (mchar_0 : addr -> Z) (s1_0 : addr) (s2_0 : addr) (n : Z), if decide (n = 0%Z) then l_strncmp_2' mchar_0 s1_0 s2_0 n = 0%Z else if decide (mchar_0 (shift s2_0 0%Z) = mchar_0 (shift s1_0 0%Z)) then if decide (mchar_0 (shift s1_0 0%Z) = 0%Z) then l_strncmp_2' mchar_0 s1_0 s2_0 n = 0%Z else l_strncmp_2' mchar_0 (shift s1_0 1%Z) (shift s2_0 1%Z) (to_uint64 (n - 1%Z)) = l_strncmp_2' mchar_0 s1_0 s2_0 n else to_sint32 (mchar_0 (shift s1_0 0%Z) - mchar_0 (shift s2_0 0%Z)) = l_strncmp_2' mchar_0 s1_0 s2_0 n.
Definition p_strnequal (mchar_0 : addr -> Z) (s1_0 : addr) (s2_0 : addr) (n : Z) := l_strncmp_2' mchar_0 s1_0 s2_0 n = 0%Z.
Axiom Q_TL_strncmp_2' : forall  (mchar_0 : addr -> Z) (s1_0 : addr) (s2_0 : addr) (n : Z), is_sint32 (l_strncmp_2' mchar_0 s1_0 s2_0 n).
