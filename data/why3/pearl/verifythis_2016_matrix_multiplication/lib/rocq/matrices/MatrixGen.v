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
Axiom rows : forall {α : Type} `{Inhabited α}, mat α -> Z.
Axiom cols : forall {α : Type} `{Inhabited α}, mat α -> Z.
Axiom rows_and_cols_nonnegative : forall  {α : Type} `{Inhabited α} (m : mat α), 0%Z ≤ rows m ∧ 0%Z ≤ cols m.
Axiom get : forall {α : Type} `{Inhabited α}, mat α -> Z -> Z -> α.
Axiom set : forall {α : Type} `{Inhabited α}, mat α -> Z -> Z -> α -> mat α.
Axiom set_def1 : forall  {α : Type} `{Inhabited α} (i : Z) (m : mat α) (j : Z) (v : α) (fact0 : 0%Z ≤ i) (fact1 : i < rows m) (fact2 : 0%Z ≤ j) (fact3 : j < cols m), rows (set m i j v) = rows m.
Axiom set_def2 : forall  {α : Type} `{Inhabited α} (i : Z) (m : mat α) (j : Z) (v : α) (fact0 : 0%Z ≤ i) (fact1 : i < rows m) (fact2 : 0%Z ≤ j) (fact3 : j < cols m), cols (set m i j v) = cols m.
Axiom set_def3 : forall  {α : Type} `{Inhabited α} (i : Z) (m : mat α) (j : Z) (v : α) (fact0 : 0%Z ≤ i) (fact1 : i < rows m) (fact2 : 0%Z ≤ j) (fact3 : j < cols m), get (set m i j v) i j = v.
Axiom set_def4 : forall  {α : Type} `{Inhabited α} (i : Z) (m : mat α) (j : Z) (i' : Z) (j' : Z) (v : α) (fact0 : 0%Z ≤ i) (fact1 : i < rows m) (fact2 : 0%Z ≤ j) (fact3 : j < cols m) (fact4 : 0%Z ≤ i') (fact5 : i' < rows m) (fact6 : 0%Z ≤ j') (fact7 : j' < cols m) (fact8 : ¬ i = i' ∨ ¬ j = j'), get (set m i j v) i' j' = get m i' j'.
Definition infix_eqeq {α : Type} `{Inhabited α} (m1 : mat α) (m2 : mat α) := rows m1 = rows m2 ∧ cols m1 = cols m2 ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < rows m1 -> 0%Z ≤ j ∧ j < cols m1 -> get m1 i j = get m2 i j).
Axiom extensionality : forall  {α : Type} `{Inhabited α} (m1 : mat α) (m2 : mat α) (fact0 : infix_eqeq m1 m2), m1 = m2.
Definition infix_eqeqeq {α : Type} `{Inhabited α} (a : mat α) (b : mat α) := rows a = rows b ∧ cols a = cols b.
