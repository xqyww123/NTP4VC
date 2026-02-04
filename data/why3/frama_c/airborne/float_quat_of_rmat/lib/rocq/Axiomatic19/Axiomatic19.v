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
Require Import float_quat_of_rmat.S10_RealRMat_s.S10_RealRMat_s.
Require Import Why3.Memory.Memory.
Require Import float_quat_of_rmat.Axiomatic17.Axiomatic17.
Require Import float_quat_of_rmat.Compound.Compound.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_quat_of_rmat.S11_RealQuat_s.S11_RealQuat_s.
Require Import Why3.Square.Square.
Open Scope Z_scope.
Definition l_trace_1' (rmat_0 : s10_realrmat_s) : R := Rplus (Rplus (f10_realrmat_s_a00 rmat_0) (f10_realrmat_s_a11 rmat_0)) (f10_realrmat_s_a22 rmat_0).
Definition l_trace_2' (mflt_0 : addr -> R) (rmat_0 : addr) : R := l_trace_1' (l_l_rmat_of_floatrmat mflt_0 rmat_0).
Definition l_l_floatquat_of_rmat_trace_pos_1' (rmat_0 : s10_realrmat_s) : s11_realquat_s := let r : R := Rdiv (Rdiv 1%R 2%R) (sqrt (Rplus 1%R (l_trace_1' rmat_0))) in s11_realquat_s'mk (Rdiv (Rdiv 1%R 4%R) r) (Rmult (Rminus (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a12 rmat_0)) r) (Rmult (Rminus (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a20 rmat_0)) r) (Rmult (Rminus (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a01 rmat_0)) r).
Definition l_l_floatquat_of_rmat_trace_pos_t (mflt_0 : addr -> R) (rmat_0 : addr) : s11_realquat_s := l_l_floatquat_of_rmat_trace_pos_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0)).
Definition l_l_floatquat_of_rmat_0_max_1' (rmat_0 : s10_realrmat_s) : s11_realquat_s := let r : R := sqrt (Rminus (Rminus (Rplus 1%R (f10_realrmat_s_a00 rmat_0)) (f10_realrmat_s_a11 rmat_0)) (f10_realrmat_s_a22 rmat_0)) in let r_1 : R := Rmult 2%R r in s11_realquat_s'mk (Rdiv (Rminus (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a12 rmat_0)) r_1) (Rmult (Rdiv 1%R 2%R) r) (Rdiv (Rplus (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a10 rmat_0)) r_1) (Rdiv (Rplus (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a20 rmat_0)) r_1).
Definition l_l_floatquat_of_rmat_0_max_t (mflt_0 : addr -> R) (rmat_0 : addr) : s11_realquat_s := l_l_floatquat_of_rmat_0_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0)).
Definition l_l_floatquat_of_rmat_1_max_1' (rmat_0 : s10_realrmat_s) : s11_realquat_s := let r : R := sqrt (Rminus (Rminus (Rplus 1%R (f10_realrmat_s_a11 rmat_0)) (f10_realrmat_s_a00 rmat_0)) (f10_realrmat_s_a22 rmat_0)) in let r_1 : R := Rmult 2%R r in s11_realquat_s'mk (Rdiv (Rminus (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a20 rmat_0)) r_1) (Rdiv (Rplus (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a10 rmat_0)) r_1) (Rmult (Rdiv 1%R 2%R) r) (Rdiv (Rplus (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a21 rmat_0)) r_1).
Definition l_l_floatquat_of_rmat_1_max_t (mflt_0 : addr -> R) (rmat_0 : addr) : s11_realquat_s := l_l_floatquat_of_rmat_1_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0)).
Definition l_l_floatquat_of_rmat_2_max_1' (rmat_0 : s10_realrmat_s) : s11_realquat_s := let r : R := sqrt (Rminus (Rminus (Rplus 1%R (f10_realrmat_s_a22 rmat_0)) (f10_realrmat_s_a00 rmat_0)) (f10_realrmat_s_a11 rmat_0)) in let r_1 : R := Rmult 2%R r in s11_realquat_s'mk (Rdiv (Rminus (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a01 rmat_0)) r_1) (Rdiv (Rplus (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a20 rmat_0)) r_1) (Rdiv (Rplus (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a21 rmat_0)) r_1) (Rmult (Rdiv 1%R 2%R) r).
Definition l_l_floatquat_of_rmat_2_max_t (mflt_0 : addr -> R) (rmat_0 : addr) : s11_realquat_s := l_l_floatquat_of_rmat_2_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0)).
