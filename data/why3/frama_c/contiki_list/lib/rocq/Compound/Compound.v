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
Require Import contiki_list.S1_list.S1_list.
Open Scope Z_scope.
Definition load_s1_list (p : addr) (mflt_0 : addr -> R) (mptr_0 : addr -> addr) : s1_list := s1_list'mk (mptr_0 (shift p 0%Z)) (mflt_0 (shift p 1%Z)) (mflt_0 (shift p 2%Z)) (mflt_0 (shift p 3%Z)).
Axiom Q_Load_S1_list_update_Mflt : forall  (p : addr) (q : addr) (mflt_0 : addr -> R) (v : R) (mptr_0 : addr -> addr) (fact0 : separated p 4%Z q 1%Z), load_s1_list p (fun_updt mflt_0 q v) mptr_0 = load_s1_list p mflt_0 mptr_0.
Axiom Q_Load_S1_list_eqmem_Mflt : forall  (p : addr) (q : addr) (k : Z) (mflt_0 : addr -> R) (mflt_1 : addr -> R) (mptr_0 : addr -> addr) (fact0 : included p 4%Z q k) (fact1 : eqmem mflt_0 mflt_1 q k), load_s1_list p mflt_1 mptr_0 = load_s1_list p mflt_0 mptr_0.
Axiom Q_Load_S1_list_havoc_Mflt : forall  (mflt_2 : addr -> R) (mflt_0 : addr -> R) (q : addr) (k : Z) (mflt_1 : addr -> R) (p : addr) (mptr_0 : addr -> addr) (fact0 : havoc mflt_2 mflt_0 q k = mflt_1) (fact1 : separated p 4%Z q k), load_s1_list p mflt_1 mptr_0 = load_s1_list p mflt_0 mptr_0.
Axiom Q_Load_S1_list_update_Mptr : forall  (p : addr) (q : addr) (mflt_0 : addr -> R) (mptr_0 : addr -> addr) (v : addr) (fact0 : separated p 4%Z q 1%Z), load_s1_list p mflt_0 (fun_updt mptr_0 q v) = load_s1_list p mflt_0 mptr_0.
Axiom Q_Load_S1_list_eqmem_Mptr : forall  (p : addr) (q : addr) (k : Z) (mptr_0 : addr -> addr) (mptr_1 : addr -> addr) (mflt_0 : addr -> R) (fact0 : included p 4%Z q k) (fact1 : eqmem mptr_0 mptr_1 q k), load_s1_list p mflt_0 mptr_1 = load_s1_list p mflt_0 mptr_0.
Axiom Q_Load_S1_list_havoc_Mptr : forall  (mptr_2 : addr -> addr) (mptr_0 : addr -> addr) (q : addr) (k : Z) (mptr_1 : addr -> addr) (p : addr) (mflt_0 : addr -> R) (fact0 : havoc mptr_2 mptr_0 q k = mptr_1) (fact1 : separated p 4%Z q k), load_s1_list p mflt_0 mptr_1 = load_s1_list p mflt_0 mptr_0.
