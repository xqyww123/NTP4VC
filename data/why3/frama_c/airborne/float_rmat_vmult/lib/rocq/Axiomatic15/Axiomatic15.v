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
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_vmult.Compound.Compound.
Open Scope Z_scope.
Definition p_finite_floatvect3 (mflt_0 : addr -> R) (v : addr) := is_finite32 (mflt_0 (shift v 0%Z)) ∧ is_finite32 (mflt_0 (shift v 1%Z)) ∧ is_finite32 (mflt_0 (shift v 2%Z)).
Definition p_rvalid_floatvect3 (malloc_0 : Z -> Z) (mflt_0 : addr -> R) (v : addr) := p_finite_floatvect3 mflt_0 v ∧ valid_rd malloc_0 v 3%Z.
Definition p_finite_floatrmat (mflt_0 : addr -> R) (rm_0 : addr) := let a : addr := shift rm_0 0%Z in is_finite32 (mflt_0 (shift a 0%Z)) ∧ is_finite32 (mflt_0 (shift a 1%Z)) ∧ is_finite32 (mflt_0 (shift a 2%Z)) ∧ is_finite32 (mflt_0 (shift a 3%Z)) ∧ is_finite32 (mflt_0 (shift a 4%Z)) ∧ is_finite32 (mflt_0 (shift a 5%Z)) ∧ is_finite32 (mflt_0 (shift a 6%Z)) ∧ is_finite32 (mflt_0 (shift a 7%Z)) ∧ is_finite32 (mflt_0 (shift a 8%Z)).
Definition p_rvalid_floatrmat (malloc_0 : Z -> Z) (mflt_0 : addr -> R) (rm_0 : addr) := p_finite_floatrmat mflt_0 rm_0 ∧ valid_rd malloc_0 rm_0 9%Z.
