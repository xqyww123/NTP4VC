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
Require Import float_rmat_of_quat.S10_RealRMat_s.S10_RealRMat_s.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_of_quat.Compound.Compound.
Open Scope Z_scope.
Definition l_l_rmat_of_floatquat_1' (mflt_0 : addr -> R) (q : addr) : s10_realrmat_s := let r : R := mflt_0 (shift q 2%Z) in let r_1 : R := Rmult r r in let r_2 : R := Ropp r_1 in let r_3 : R := mflt_0 (shift q 3%Z) in let r_4 : R := Rmult r_3 r_3 in let r_5 : R := Ropp r_4 in let r_6 : R := mflt_0 (shift q 0%Z) in let r_7 : R := Rmult r_6 r_6 in let r_8 : R := mflt_0 (shift q 1%Z) in let r_9 : R := Rmult r_8 r_8 in let r_10 : R := Rmult r_6 r_3 in let r_11 : R := Rmult r_8 r in let r_12 : R := Rmult r_6 r in let r_13 : R := Rmult r_8 r_3 in let r_14 : R := Ropp r_9 in let r_15 : R := Rmult r_6 r_8 in let r_16 : R := Rmult r r_3 in s10_realrmat_s'mk (Rminus (Rminus (Rplus r_7 r_9) r_1) r_4) (Rmult 2%R (Rminus r_11 r_10)) (Rmult 2%R (Rplus r_12 r_13)) (Rmult 2%R (Rplus r_10 r_11)) (Rminus (Rminus (Rplus r_7 r_1) r_9) r_4) (Rmult 2%R (Rminus r_16 r_15)) (Rmult 2%R (Rminus r_13 r_12)) (Rmult 2%R (Rplus r_15 r_16)) (Rminus (Rminus (Rplus r_7 r_4) r_9) r_1).
Definition p_unitary_quaternion_1' (mflt_0 : addr -> R) (q : addr) := let r : R := mflt_0 (shift q 0%Z) in let r_1 : R := mflt_0 (shift q 1%Z) in let r_2 : R := mflt_0 (shift q 2%Z) in let r_3 : R := mflt_0 (shift q 3%Z) in Rplus (Rplus (Rplus (Rmult r r) (Rmult r_1 r_1)) (Rmult r_2 r_2)) (Rmult r_3 r_3) = 1%R.
