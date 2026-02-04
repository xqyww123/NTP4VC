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
Require Import Why3.int.Sum.
Require Import verifythis_2016_matrix_multiplication.matrices.MyMatrix.
Require Import verifythis_2016_matrix_multiplication.sum_extended.Sum_extended.
Open Scope Z_scope.
Axiom zerof : Z -> Z -> Z.
Axiom zerof'def : forall  (x : Z) (x_1 : Z), zerof x x_1 = 0%Z.
Axiom add2f : mat Z -> mat Z -> Z -> Z -> Z.
Axiom add2f'def : forall  (a : mat Z) (b : mat Z) (x : Z) (y : Z), add2f a b x y = get a x y + get b x y.
Definition add (a : mat Z) (b : mat Z) : mat Z := create (rows a) (cols a) (add2f a b).
Axiom opp2f : mat Z -> Z -> Z -> Z.
Axiom opp2f'def : forall  (a : mat Z) (x : Z) (y : Z), opp2f a x y = - get a x y.
Definition opp (a : mat Z) : mat Z := create (rows a) (cols a) (opp2f a).
Definition sub (a : mat Z) (b : mat Z) : mat Z := add a (opp b).
Axiom mul_atom : mat Z -> mat Z -> Z -> Z -> Z -> Z.
Axiom mul_atom'def : forall  (a : mat Z) (b : mat Z) (i : Z) (j : Z) (k : Z), mul_atom a b i j k = get a i k * get b k j.
Axiom mul_cell : mat Z -> mat Z -> Z -> Z -> Z.
Axiom mul_cell'def : forall  (a : mat Z) (b : mat Z) (i : Z) (j : Z), mul_cell a b i j = sum (mul_atom a b i j) 0%Z (cols a).
Definition mul (a : mat Z) (b : mat Z) : mat Z := create (rows a) (cols b) (mul_cell a b).
Axiom ft1 : mat Z -> mat Z -> mat Z -> Z -> Z -> Z -> Z -> Z.
Axiom ft1'def : forall  (a : mat Z) (b : mat Z) (c : mat Z) (i : Z) (j : Z) (k : Z), ft1 a b c i j k = smulf (mul_atom a b i k) (get c k j).
Axiom ft2 : mat Z -> mat Z -> mat Z -> Z -> Z -> Z -> Z -> Z.
Axiom ft2'def : forall  (a : mat Z) (b : mat Z) (c : mat Z) (i : Z) (j : Z) (k : Z), ft2 a b c i j k = smulf (mul_atom b c k j) (get a i k).
