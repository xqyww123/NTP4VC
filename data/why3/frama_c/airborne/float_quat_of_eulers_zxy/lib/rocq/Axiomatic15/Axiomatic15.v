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
Require Import float_quat_of_eulers_zxy.Compound.Compound.
Open Scope Z_scope.
Definition p_finite_floateulers (mflt_0 : addr -> R) (e : addr) := is_finite32 (mflt_0 (shift e 0%Z)) ∧ is_finite32 (mflt_0 (shift e 2%Z)) ∧ is_finite32 (mflt_0 (shift e 1%Z)).
Definition p_rvalid_floateulers (malloc_0 : Z -> Z) (mflt_0 : addr -> R) (e : addr) := p_finite_floateulers mflt_0 e ∧ valid_rd malloc_0 e 3%Z.
