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
Require Import verker.A_StrCmp.A_StrCmp.
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Axiom l_match_string : (addr -> addr) -> (addr -> Z) -> addr -> Z -> addr -> Z.
Axiom fix_l_match_string : forall  (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (a : addr) (n : Z) (s : addr), if decide (n = 0%Z) then l_match_string mptr_0 mchar_0 a n s = 0%Z else if decide (l_strcmp mchar_0 (mptr_0 (shift a 0%Z)) s = 0%Z) then l_match_string mptr_0 mchar_0 a n s = 0%Z else l_match_string mptr_0 mchar_0 (shift a 1%Z) (to_uint64 (n - 1%Z)) s = l_match_string mptr_0 mchar_0 a n s.
Axiom l_real_len : (addr -> addr) -> addr -> Z -> Z.
Axiom fix_l_real_len : forall  (mptr_0 : addr -> addr) (a : addr) (n : Z), if decide (n = 0%Z ∨ mptr_0 (shift a 0%Z) = Mk_addr 0%Z 0%Z) then l_real_len mptr_0 a n = 0%Z else to_uint64 (1%Z + l_real_len mptr_0 (shift a 1%Z) (to_uint64 (n - 1%Z))) = l_real_len mptr_0 a n.
Axiom Q_TL_match_string : forall  (mptr_0 : addr -> addr) (mchar_0 : addr -> Z) (a : addr) (n : Z) (s : addr), is_uint64 (l_match_string mptr_0 mchar_0 a n s).
Axiom Q_TL_real_len : forall  (mptr_0 : addr -> addr) (a : addr) (n : Z), is_uint64 (l_real_len mptr_0 a n).
