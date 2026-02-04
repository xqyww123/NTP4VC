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
Open Scope Z_scope.
Axiom mat : Type -> Type.
Axiom mat_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (mat α).
Global Existing Instance mat_inhabited.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Axiom zero : t.
Axiom infix_pl : t -> t -> t.
Axiom prefix_mn : t -> t.
Axiom infix_as : t -> t -> t.
Axiom Assoc : forall  (x : t) (y : t) (z : t), infix_pl (infix_pl x y) z = infix_pl x (infix_pl y z).
Axiom Unit_def_l : forall  (x : t), infix_pl zero x = x.
Axiom Unit_def_r : forall  (x : t), infix_pl x zero = x.
Axiom Inv_def_l : forall  (x : t), infix_pl (prefix_mn x) x = zero.
Axiom Inv_def_r : forall  (x : t), infix_pl x (prefix_mn x) = zero.
Axiom Comm : forall  (x : t) (y : t), infix_pl x y = infix_pl y x.
Axiom Assoc1 : forall  (x : t) (y : t) (z : t), infix_as (infix_as x y) z = infix_as x (infix_as y z).
Axiom Mul_distr_l : forall  (x : t) (y : t) (z : t), infix_as x (infix_pl y z) = infix_pl (infix_as x y) (infix_as x z).
Axiom Mul_distr_r : forall  (y : t) (z : t) (x : t), infix_as (infix_pl y z) x = infix_pl (infix_as y x) (infix_as z x).
Axiom Comm1 : forall  (x : t) (y : t), infix_as x y = infix_as y x.
Axiom one : t.
Axiom Unitary : forall  (x : t), infix_as one x = x.
Axiom NonTrivialRing : ¬ zero = one.
Axiom get : mat t -> Z -> Z -> t.
Axiom set : mat t -> Z -> Z -> t -> mat t.
Axiom row_zeros : mat t -> Z -> Z.
Axiom col_zeros : mat t -> Z -> Z.
Axiom row_zeros_def : forall  (i : Z) (m : mat t) (j : Z) (fact0 : 0%Z ≤ i) (fact1 : row_zeros m i ≤ j), get m i j = zero.
Axiom col_zeros_def : forall  (j : Z) (m : mat t) (i : Z) (fact0 : 0%Z ≤ j) (fact1 : col_zeros m j ≤ i), get m i j = zero.
Axiom row_zeros_nonneg : forall  (i : Z) (m : mat t) (fact0 : 0%Z ≤ i), 0%Z ≤ row_zeros m i.
Axiom col_zeros_nonneg : forall  (j : Z) (m : mat t) (fact0 : 0%Z ≤ j), 0%Z ≤ col_zeros m j.
Axiom set_def_changed : forall  (i : Z) (j : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j), get (set m i j v) i j = v.
Axiom set_def_unchanged : forall  (i : Z) (j : Z) (i' : Z) (j' : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ i') (fact3 : 0%Z ≤ j') (fact4 : ¬ i = i' ∨ ¬ j = j'), get (set m i j v) i' j' = get m i' j'.
Axiom set_def_rowz_changed : forall  (i : Z) (j : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : row_zeros m i ≤ j), row_zeros (set m i j v) i = j + 1%Z.
Axiom set_def_colz_changed : forall  (i : Z) (j : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : col_zeros m j ≤ i), col_zeros (set m i j v) j = i + 1%Z.
Axiom set_def_rowz_unchanged : forall  (i : Z) (j : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : j < row_zeros m i), row_zeros (set m i j v) i = row_zeros m i.
Axiom set_def_colz_unchanged : forall  (i : Z) (j : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : i < col_zeros m j), col_zeros (set m i j v) j = col_zeros m j.
Axiom set_def_other_rowz : forall  (i : Z) (j : Z) (i' : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ i') (fact3 : ¬ i = i'), row_zeros (set m i j v) i' = row_zeros m i'.
Axiom set_def_other_colz : forall  (i : Z) (j : Z) (j' : Z) (m : mat t) (v : t) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ j') (fact3 : ¬ j = j'), col_zeros (set m i j v) j' = col_zeros m j'.
Definition infix_eqeq (m1 : mat t) (m2 : mat t) := ∀(i : Z) (j : Z), 0%Z ≤ i -> 0%Z ≤ j -> get m1 i j = get m2 i j.
Axiom extensionality : forall  (m1 : mat t) (m2 : mat t) (fact0 : infix_eqeq m1 m2), m1 = m2.
Definition infix_eqeqeq (m1 : mat t) (m2 : mat t) := ∀(i : Z) (j : Z), 0%Z ≤ i -> 0%Z ≤ j -> row_zeros m1 i = row_zeros m2 i ∧ col_zeros m1 j = col_zeros m2 j.
Definition in_bounds (m : mat t) (i : Z) (j : Z) := (0%Z ≤ i ∧ i < col_zeros m j) ∧ 0%Z ≤ j ∧ j < row_zeros m i.
Definition size (m : mat t) (r : Z) (c : Z) := (∀(i : Z), 0%Z ≤ i -> row_zeros m i = c) ∧ (∀(j : Z), 0%Z ≤ j -> col_zeros m j = r).
