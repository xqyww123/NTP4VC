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
Require Import Why3.map.MapEq.
Require Import Why3.mach.int.Unsigned.
Require Import Why3.mach.c.C.
Open Scope Z_scope.
Axiom cursor : Type.
Axiom cursor_inhabited : Inhabited cursor.
Global Existing Instance cursor_inhabited.
Axiom cursor_countable : Countable cursor.
Global Existing Instance cursor_countable.
Axiom current : cursor -> ptr (bv 32%N).
Axiom new : cursor -> bool.
Axiom len : cursor -> bv 32%N.
Axiom freed : cursor -> bool.
Axiom bound : cursor -> bv 32%N.
Axiom cursor'invariant : forall  (self : cursor), 0%Z < bv_signed (len self) ∧ (¬ freed self = true -> plength (current self) = bv_signed (len self) ∧ offset (current self) = 0%Z ∧ valid (current self) (bv_signed (len self)) ∧ min (current self) = 0%Z ∧ C.max (current self) = bv_signed (len self) ∧ is_not_null (current self) ∧ writable (current self) = true ∧ (∀(i : Z), 0%Z ≤ i ∧ i < bv_signed (len self) -> bv_signed (nth (Z.to_nat i) (data (current self)) inhabitant) < bv_signed (bound self))).
Definition cursor'eq (a : cursor) (b : cursor) := current a = current b ∧ new a = new b ∧ len a = len b ∧ freed a = freed b ∧ bound a = bound b.
Axiom cursor'inj : forall  (a : cursor) (b : cursor) (fact0 : cursor'eq a b), a = b.
