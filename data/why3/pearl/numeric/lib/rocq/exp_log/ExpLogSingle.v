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
Require Import Why3.real.Sum.
Require Import Why3.ieee_float.RoundingMode.
Require Import Why3.ufloat.USingle.
Require Import Why3.ufloat.HelperLemmas.
Require Import Why3.ufloat.USingleLemmas.
Open Scope Z_scope.
Axiom log_error : R.
Axiom log_error_bounds : Rle 0%R log_error ∧ Rle log_error 1%R.
Axiom log_cst_error : R.
Axiom log_cst_error_bounds : Rle 0%R log_cst_error ∧ Rle log_cst_error 1%R.
Axiom log_approx : usingle -> usingle.
Axiom log_approx'spec : forall  (x : usingle) (fact0 : Rlt 0%R (to_real x)), Rle (Rabs (Rminus (to_real (log_approx x)) (ln (to_real x)))) (Rplus (Rmult (Rabs (ln (to_real x))) log_error) log_cst_error).
Axiom log2_error : R.
Axiom log2_error_bounds : Rle 0%R log2_error ∧ Rle log2_error 1%R.
Axiom log2_approx : usingle -> usingle.
Axiom log2_approx'spec : forall  (x : usingle) (fact0 : Rlt 0%R (to_real x)), Rle (Rabs (Rminus (to_real (log2_approx x)) (Rlog 2 (to_real x)))) (Rmult (Rabs (Rlog 2 (to_real x))) log2_error).
Axiom log10_error : R.
Axiom log10_error_bounds : Rle 0%R log10_error ∧ Rle log10_error 1%R.
Axiom log10_approx : usingle -> usingle.
Axiom log10_approx'spec : forall  (x : usingle) (fact0 : Rlt 0%R (to_real x)), Rle (Rabs (Rminus (to_real (log10_approx x)) (Rlog 10 (to_real x)))) (Rmult (Rabs (Rlog 10 (to_real x))) log10_error).
Axiom exp_error : R.
Axiom exp_error_bounds : Rle 0%R exp_error ∧ Rle exp_error (Rdiv 1%R 4).
Axiom exp_approx : usingle -> usingle.
Axiom exp_approx'spec : forall  (x : usingle), Rle (Rabs (Rminus (to_real (exp_approx x)) (exp (to_real x)))) (Rmult exp_error (exp (to_real x))).
