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
Require Import lse.udouble.UDouble.
Require Import Why3.ieee_float.RoundingMode.
Require Import lse.my_exp_log.ExpLogLemmas.
Require Import lse.my_exp_log.ExpLogApprox.
Require Import lse.sum_real.Sum.
Require Import lse.my_sum.Sum.
Require Import lse.my_sum.Bound.
Require Import lse.my_sum.Combine.
Open Scope Z_scope.
Axiom exp_fun : (Z -> udouble) -> Z -> R.
Axiom exp_fun'def : forall  (a : Z -> udouble) (i : Z), exp_fun a i = exp (real_fun a i).
Axiom u_exp_fun : (Z -> udouble) -> Z -> udouble.
Axiom u_exp_fun'def : forall  (a : Z -> udouble) (i : Z), u_exp_fun a i = u_exp (a i).
Definition u_sum_of_u_exp (a : Z -> udouble) (m : Z) (n : Z) : udouble := u_sum (u_exp_fun a) m n.
Definition lse_exact (f : Z -> udouble) (size : Z) : R := ln (sum (exp_fun f) 0%Z size).
