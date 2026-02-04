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
Require Import float_rmat_transp_vmult.S10_RealRMat_s.S10_RealRMat_s.
Require Import float_rmat_transp_vmult.Compound.Compound.
Require Import float_rmat_transp_vmult.S9_RealVect3_s.S9_RealVect3_s.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Open Scope Z_scope.
Definition l_l_rmat_of_floatrmat (mflt_0 : addr -> R) (rmat_0 : addr) : s10_realrmat_s := let a : addr := shift rmat_0 0%Z in s10_realrmat_s'mk (mflt_0 (shift a 0%Z)) (mflt_0 (shift a 1%Z)) (mflt_0 (shift a 2%Z)) (mflt_0 (shift a 3%Z)) (mflt_0 (shift a 4%Z)) (mflt_0 (shift a 5%Z)) (mflt_0 (shift a 6%Z)) (mflt_0 (shift a 7%Z)) (mflt_0 (shift a 8%Z)).
Definition l_transpose (rmat_0 : s10_realrmat_s) : s10_realrmat_s := s10_realrmat_s'mk (f10_realrmat_s_a00 rmat_0) (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a20 rmat_0) (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a11 rmat_0) (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a22 rmat_0).
Definition l_mult_realrmat_realvect3 (rm_0 : s10_realrmat_s) (v : s9_realvect3_s) : s9_realvect3_s := let r : R := f9_realvect3_s_x v in let r_1 : R := f9_realvect3_s_y v in let r_2 : R := f9_realvect3_s_z v in s9_realvect3_s'mk (Rplus (Rplus (Rmult (f10_realrmat_s_a00 rm_0) r) (Rmult (f10_realrmat_s_a01 rm_0) r_1)) (Rmult (f10_realrmat_s_a02 rm_0) r_2)) (Rplus (Rplus (Rmult (f10_realrmat_s_a10 rm_0) r) (Rmult (f10_realrmat_s_a11 rm_0) r_1)) (Rmult (f10_realrmat_s_a12 rm_0) r_2)) (Rplus (Rplus (Rmult (f10_realrmat_s_a20 rm_0) r) (Rmult (f10_realrmat_s_a21 rm_0) r_1)) (Rmult (f10_realrmat_s_a22 rm_0) r_2)).
