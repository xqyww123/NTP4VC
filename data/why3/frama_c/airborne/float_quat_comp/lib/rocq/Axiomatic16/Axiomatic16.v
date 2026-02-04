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
Require Import float_quat_comp.S9_RealVect3_s.S9_RealVect3_s.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Open Scope Z_scope.
Definition l_scalar_product (v1_0 : s9_realvect3_s) (v2_0 : s9_realvect3_s) : R := Rplus (Rplus (Rmult (f9_realvect3_s_x v1_0) (f9_realvect3_s_x v2_0)) (Rmult (f9_realvect3_s_y v1_0) (f9_realvect3_s_y v2_0))) (Rmult (f9_realvect3_s_z v1_0) (f9_realvect3_s_z v2_0)).
Definition l_mult_scalar_1' (scal_0 : R) (v : s9_realvect3_s) : s9_realvect3_s := s9_realvect3_s'mk (Rmult scal_0 (f9_realvect3_s_x v)) (Rmult scal_0 (f9_realvect3_s_y v)) (Rmult scal_0 (f9_realvect3_s_z v)).
Definition l_add_realvect3 (v1_0 : s9_realvect3_s) (v2_0 : s9_realvect3_s) : s9_realvect3_s := s9_realvect3_s'mk (Rplus (f9_realvect3_s_x v1_0) (f9_realvect3_s_x v2_0)) (Rplus (f9_realvect3_s_y v1_0) (f9_realvect3_s_y v2_0)) (Rplus (f9_realvect3_s_z v1_0) (f9_realvect3_s_z v2_0)).
Definition l_cross_product (v1_0 : s9_realvect3_s) (v2_0 : s9_realvect3_s) : s9_realvect3_s := let r : R := f9_realvect3_s_z v1_0 in let r_1 : R := f9_realvect3_s_y v2_0 in let r_2 : R := f9_realvect3_s_y v1_0 in let r_3 : R := f9_realvect3_s_z v2_0 in let r_4 : R := f9_realvect3_s_x v1_0 in let r_5 : R := f9_realvect3_s_x v2_0 in s9_realvect3_s'mk (Rplus (Ropp (Rmult r r_1)) (Rmult r_2 r_3)) (Rplus (Ropp (Rmult r_4 r_3)) (Rmult r r_5)) (Rplus (Ropp (Rmult r_2 r_5)) (Rmult r_4 r_1)).
