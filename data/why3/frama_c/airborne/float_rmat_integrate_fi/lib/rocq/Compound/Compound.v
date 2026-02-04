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
Require Import float_rmat_integrate_fi.S5_FloatRMat.S5_FloatRMat.
Open Scope Z_scope.
Axiom array1_float : addr -> Z -> (addr -> R) -> Z -> R.
Definition load_s5_floatrmat (p : addr) (mflt_0 : addr -> R) : s5_floatrmat := s5_floatrmat'mk (array1_float (shift p 0%Z) 9%Z mflt_0).
Axiom Q_Array1_float_access : forall  (i : Z) (n : Z) (p : addr) (mflt_0 : addr -> R) (fact0 : 0%Z ≤ i) (fact1 : i < n), array1_float p n mflt_0 i = mflt_0 (shift p i).
Axiom Q_Array1_float_update_Mflt : forall  (p : addr) (n : Z) (q : addr) (mflt_0 : addr -> R) (v : R) (fact0 : separated p n q 1%Z), array1_float p n (fun_updt mflt_0 q v) = array1_float p n mflt_0.
Axiom Q_Array1_float_eqmem_Mflt : forall  (p : addr) (n : Z) (q : addr) (k : Z) (mflt_0 : addr -> R) (mflt_1 : addr -> R) (fact0 : included p n q k) (fact1 : eqmem mflt_0 mflt_1 q k), array1_float p n mflt_1 = array1_float p n mflt_0.
Axiom Q_Array1_float_havoc_Mflt : forall  (mflt_2 : addr -> R) (mflt_0 : addr -> R) (q : addr) (k : Z) (mflt_1 : addr -> R) (p : addr) (n : Z) (fact0 : havoc mflt_2 mflt_0 q k = mflt_1) (fact1 : separated p n q k), array1_float p n mflt_1 = array1_float p n mflt_0.
Axiom Q_Load_S5_FloatRMat_update_Mflt : forall  (p : addr) (q : addr) (mflt_0 : addr -> R) (v : R) (fact0 : separated p 9%Z q 1%Z), load_s5_floatrmat p (fun_updt mflt_0 q v) = load_s5_floatrmat p mflt_0.
Axiom Q_Load_S5_FloatRMat_eqmem_Mflt : forall  (p : addr) (q : addr) (k : Z) (mflt_0 : addr -> R) (mflt_1 : addr -> R) (fact0 : included p 9%Z q k) (fact1 : eqmem mflt_0 mflt_1 q k), load_s5_floatrmat p mflt_1 = load_s5_floatrmat p mflt_0.
Axiom Q_Load_S5_FloatRMat_havoc_Mflt : forall  (mflt_2 : addr -> R) (mflt_0 : addr -> R) (q : addr) (k : Z) (mflt_1 : addr -> R) (p : addr) (fact0 : havoc mflt_2 mflt_0 q k = mflt_1) (fact1 : separated p 9%Z q k), load_s5_floatrmat p mflt_1 = load_s5_floatrmat p mflt_0.
