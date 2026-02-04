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
Definition l_cmp (a : Z) (b : Z) : Z := if decide (b = a) then 0%Z else if decide (a < b) then - 1%Z else 1%Z.
Axiom l_strncmp_1' : (addr -> Z) -> addr -> addr -> Z -> Z.
Axiom fix_l_strncmp_1' : forall  (mchar_0 : addr -> Z) (cs_0 : addr) (ct_0 : addr) (n : Z), if decide (n = - 1%Z) then l_strncmp_1' mchar_0 cs_0 ct_0 n = 0%Z else if decide (mchar_0 (shift ct_0 0%Z) = mchar_0 (shift cs_0 0%Z)) then l_strncmp_1' mchar_0 (shift cs_0 1%Z) (shift ct_0 1%Z) (n - 1%Z) = l_strncmp_1' mchar_0 cs_0 ct_0 n else l_cmp (to_uint8 (mchar_0 (shift cs_0 0%Z))) (to_uint8 (mchar_0 (shift ct_0 0%Z))) = l_strncmp_1' mchar_0 cs_0 ct_0 n.
Definition l_strcmp (mchar_0 : addr -> Z) (cs_0 : addr) (ct_0 : addr) : Z := l_strncmp_1' mchar_0 cs_0 ct_0 (l_strlen mchar_0 cs_0).
Definition p_equaln (mchar_0 : addr -> Z) (cs_0 : addr) (ct_0 : addr) (n : Z) := l_strncmp_1' mchar_0 cs_0 ct_0 n = 0%Z.
Definition p_equal (mchar_0 : addr -> Z) (cs_0 : addr) (ct_0 : addr) := l_strcmp mchar_0 cs_0 ct_0 = 0%Z.
