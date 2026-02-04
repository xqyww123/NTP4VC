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
Axiom l_strchr : (addr -> Z) -> addr -> Z -> addr.
Axiom fix_l_strchr : forall  (mchar_0 : addr -> Z) (str_0 : addr) (c : Z), if decide (mchar_0 str_0 = c) then l_strchr mchar_0 str_0 c = str_0 else if decide (mchar_0 str_0 = 0%Z) then l_strchr mchar_0 str_0 c = Mk_addr 0%Z 0%Z else l_strchr mchar_0 (shift str_0 1%Z) c = l_strchr mchar_0 str_0 c.
