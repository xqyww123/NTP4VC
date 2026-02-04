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
Require Import Why3.why3.Ref.Ref.
Require Import Why3.real.Sum.
Require Import Why3.ieee_float.RoundingMode.
Require Import Why3.ufloat.USingle.
Require Import Why3.ufloat.HelperLemmas.
Require Import Why3.ufloat.USingleLemmas.
Open Scope Z_scope.
Axiom abs_real_fun : (Z -> usingle) -> Z -> R.
Axiom abs_real_fun'def : forall  (f : Z -> usingle) (i : Z), abs_real_fun f i = Rabs (to_real (f i)).
Axiom exact_f : Z -> R.
Axiom f' : Z -> R.
Axiom f'_def : forall  (i : Z), f' i = Rabs (exact_f i).
Axiom f_rel_err : R.
Axiom f_cst_err : R.
Axiom example1 : (Z -> usingle) -> Z -> usingle.
Axiom example1'spec : forall  (n : Z) (f : Z -> usingle) (fact0 : 0%Z ≤ n) (fact1 : ∀(i : Z), Rle (Rabs (Rminus (to_real (f i)) (exact_f i))) (Rmult (f' i) f_rel_err)), Rle (Rabs (Rminus (to_real (example1 f n)) (sum exact_f 0%Z n))) (Rmult (sum f' 0%Z n) (Rplus f_rel_err (Rmult (Rmult eps (Rdefinitions.IZR n)) (Rplus 1%R f_rel_err)))).
