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
Require Import float_quat_comp_norm_shortest.S12_RealQuatVect_s.S12_RealQuatVect_s.
Require Import float_quat_comp_norm_shortest.S9_RealVect3_s.S9_RealVect3_s.
Require Import float_quat_comp_norm_shortest.Compound.Compound.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_quat_comp_norm_shortest.Axiomatic16.Axiomatic16.
Open Scope Z_scope.
Definition l_l_quatvect_of_floatquat (mflt_0 : addr -> R) (q : addr) : s12_realquatvect_s := s12_realquatvect_s'mk (mflt_0 (shift q 0%Z)) (s9_realvect3_s'mk (mflt_0 (shift q 1%Z)) (mflt_0 (shift q 2%Z)) (mflt_0 (shift q 3%Z))).
Definition l_mult_realquatvect (q1_0 : s12_realquatvect_s) (q2_0 : s12_realquatvect_s) : s12_realquatvect_s := let a : s9_realvect3_s := f12_realquatvect_s_vect q1_0 in let a_1 : s9_realvect3_s := f12_realquatvect_s_vect q2_0 in let r : R := f12_realquatvect_s_scalar q1_0 in let r_1 : R := f12_realquatvect_s_scalar q2_0 in s12_realquatvect_s'mk (Rplus (Ropp (l_scalar_product a a_1)) (Rmult r r_1)) (l_add_realvect3 (l_add_realvect3 (l_mult_scalar_1' r a_1) (l_mult_scalar_1' r_1 a)) (l_cross_product a a_1)).
