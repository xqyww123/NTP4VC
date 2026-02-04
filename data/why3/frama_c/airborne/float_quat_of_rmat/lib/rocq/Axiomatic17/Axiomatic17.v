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
Require Import float_quat_of_rmat.S10_RealRMat_s.S10_RealRMat_s.
Require Import float_quat_of_rmat.Compound.Compound.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Open Scope Z_scope.
Definition l_l_rmat_of_floatrmat (mflt_0 : addr -> R) (rmat_0 : addr) : s10_realrmat_s := let a : addr := shift rmat_0 0%Z in s10_realrmat_s'mk (mflt_0 (shift a 0%Z)) (mflt_0 (shift a 1%Z)) (mflt_0 (shift a 2%Z)) (mflt_0 (shift a 3%Z)) (mflt_0 (shift a 4%Z)) (mflt_0 (shift a 5%Z)) (mflt_0 (shift a 6%Z)) (mflt_0 (shift a 7%Z)) (mflt_0 (shift a 8%Z)).
Definition l_determinant (rmat_0 : s10_realrmat_s) : R := let r : R := f10_realrmat_s_a00 rmat_0 in let r_1 : R := f10_realrmat_s_a12 rmat_0 in let r_2 : R := f10_realrmat_s_a21 rmat_0 in let r_3 : R := f10_realrmat_s_a01 rmat_0 in let r_4 : R := f10_realrmat_s_a10 rmat_0 in let r_5 : R := f10_realrmat_s_a22 rmat_0 in let r_6 : R := f10_realrmat_s_a02 rmat_0 in let r_7 : R := f10_realrmat_s_a11 rmat_0 in let r_8 : R := f10_realrmat_s_a20 rmat_0 in Rminus (Rminus (Rminus (Rplus (Rplus (Rmult (Rmult r r_7) r_5) (Rmult (Rmult r_3 r_1) r_8)) (Rmult (Rmult r_6 r_4) r_2)) (Rmult (Rmult r r_1) r_2)) (Rmult (Rmult r_3 r_4) r_5)) (Rmult (Rmult r_6 r_7) r_8).
Definition p_special_orthogonal (rmat_0 : s10_realrmat_s) := l_determinant rmat_0 = 1%R.
Definition l_transpose (rmat_0 : s10_realrmat_s) : s10_realrmat_s := s10_realrmat_s'mk (f10_realrmat_s_a00 rmat_0) (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a20 rmat_0) (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a11 rmat_0) (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a22 rmat_0).
Definition l_mult_realrmat (rmat1_0 : s10_realrmat_s) (rmat2_0 : s10_realrmat_s) : s10_realrmat_s := let r : R := f10_realrmat_s_a00 rmat1_0 in let r_1 : R := f10_realrmat_s_a00 rmat2_0 in let r_2 : R := f10_realrmat_s_a01 rmat1_0 in let r_3 : R := f10_realrmat_s_a10 rmat2_0 in let r_4 : R := f10_realrmat_s_a02 rmat1_0 in let r_5 : R := f10_realrmat_s_a20 rmat2_0 in let r_6 : R := f10_realrmat_s_a01 rmat2_0 in let r_7 : R := f10_realrmat_s_a11 rmat2_0 in let r_8 : R := f10_realrmat_s_a21 rmat2_0 in let r_9 : R := f10_realrmat_s_a02 rmat2_0 in let r_10 : R := f10_realrmat_s_a12 rmat2_0 in let r_11 : R := f10_realrmat_s_a22 rmat2_0 in let r_12 : R := f10_realrmat_s_a10 rmat1_0 in let r_13 : R := f10_realrmat_s_a11 rmat1_0 in let r_14 : R := f10_realrmat_s_a12 rmat1_0 in let r_15 : R := f10_realrmat_s_a20 rmat1_0 in let r_16 : R := f10_realrmat_s_a21 rmat1_0 in let r_17 : R := f10_realrmat_s_a22 rmat1_0 in s10_realrmat_s'mk (Rplus (Rplus (Rmult r r_1) (Rmult r_2 r_3)) (Rmult r_4 r_5)) (Rplus (Rplus (Rmult r r_6) (Rmult r_2 r_7)) (Rmult r_4 r_8)) (Rplus (Rplus (Rmult r r_9) (Rmult r_2 r_10)) (Rmult r_4 r_11)) (Rplus (Rplus (Rmult r_12 r_1) (Rmult r_13 r_3)) (Rmult r_14 r_5)) (Rplus (Rplus (Rmult r_12 r_6) (Rmult r_13 r_7)) (Rmult r_14 r_8)) (Rplus (Rplus (Rmult r_12 r_9) (Rmult r_13 r_10)) (Rmult r_14 r_11)) (Rplus (Rplus (Rmult r_15 r_1) (Rmult r_16 r_3)) (Rmult r_17 r_5)) (Rplus (Rplus (Rmult r_15 r_6) (Rmult r_16 r_7)) (Rmult r_17 r_8)) (Rplus (Rplus (Rmult r_15 r_9) (Rmult r_16 r_10)) (Rmult r_17 r_11)).
Definition p_rotation_matrix (rmat_0 : s10_realrmat_s) := eqs10_realrmat_s (l_mult_realrmat rmat_0 (l_transpose rmat_0)) (s10_realrmat_s'mk 1%R 0%R 0%R 0%R 1%R 0%R 0%R 0%R 1%R).
