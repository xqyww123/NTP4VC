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
Axiom t1 : Type.
Axiom t1_inhabited : Inhabited t1.
Global Existing Instance t1_inhabited.
Axiom t1_countable : Countable t1.
Global Existing Instance t1_countable.
Axiom zero1 : t1.
Axiom infix_pl' : t1 -> t1 -> t1.
Axiom prefix_mn' : t1 -> t1.
Axiom infix_as' : t1 -> t1 -> t1.
Axiom Assoc2 : forall  (x : t1) (y : t1) (z : t1), infix_pl' (infix_pl' x y) z = infix_pl' x (infix_pl' y z).
Axiom Unit_def_l1 : forall  (x : t1), infix_pl' zero1 x = x.
Axiom Unit_def_r1 : forall  (x : t1), infix_pl' x zero1 = x.
Axiom Inv_def_l1 : forall  (x : t1), infix_pl' (prefix_mn' x) x = zero1.
Axiom Inv_def_r1 : forall  (x : t1), infix_pl' x (prefix_mn' x) = zero1.
Axiom Comm2 : forall  (x : t1) (y : t1), infix_pl' x y = infix_pl' y x.
Axiom Assoc3 : forall  (x : t1) (y : t1) (z : t1), infix_as' (infix_as' x y) z = infix_as' x (infix_as' y z).
Axiom Mul_distr_l1 : forall  (x : t1) (y : t1) (z : t1), infix_as' x (infix_pl' y z) = infix_pl' (infix_as' x y) (infix_as' x z).
Axiom Mul_distr_r1 : forall  (y : t1) (z : t1) (x : t1), infix_as' (infix_pl' y z) x = infix_pl' (infix_as' y x) (infix_as' z x).
Axiom Comm3 : forall  (x : t1) (y : t1), infix_as' x y = infix_as' y x.
Axiom one1 : t1.
Axiom Unitary1 : forall  (x : t1), infix_as' one1 x = x.
Axiom NonTrivialRing1 : ¬ zero1 = one1.
Axiom morph : t1 -> t.
Axiom morph_zero : morph zero1 = zero.
Axiom morph_one : morph one1 = one.
Axiom morph_add : forall  (z1 : t1) (z2 : t1), morph (infix_pl' z1 z2) = infix_pl (morph z1) (morph z2).
Axiom morph_mul : forall  (z1 : t1) (z2 : t1), morph (infix_as' z1 z2) = infix_as (morph z1) (morph z2).
Axiom morph_inv : forall  (z : t1), morph (prefix_mn' z) = prefix_mn (morph z).
Axiom eq0 : t1 -> Prop.
Axiom eq0'spec : forall  (x : t1), eq0 x = (x = zero1).
Inductive t2 :=
  | Var : Z -> t2
  | Add : t2 -> t2 -> t2
  | Mul : t2 -> t2 -> t2
  | Cst : t1 -> t2.
Axiom t2_inhabited : Inhabited t2.
Global Existing Instance t2_inhabited.
Axiom t2_countable : Countable t2.
Global Existing Instance t2_countable.
Axiom vars : Type.
Axiom vars_inhabited : Inhabited vars.
Global Existing Instance vars_inhabited.
Axiom vars_countable : Countable vars.
Global Existing Instance vars_countable.
Program Fixpoint interp (x : t2) (y : Z -> t) : t :=
match x with | Var n => y n | Add x1 x2 => infix_pl (interp x1 y) (interp x2 y) | Mul x1 x2 => infix_as (interp x1 y) (interp x2 y) | Cst c => morph c end.
Admit Obligations.
Definition eq (x1 : t2) (x2 : t2) := ∀(y : Z -> t), interp x1 y = interp x2 y.
Inductive m :=
  | M : t1 -> list Z -> m.
Axiom m_inhabited : Inhabited m.
Global Existing Instance m_inhabited.
Axiom m_countable : Countable m.
Global Existing Instance m_countable.
Axiom t' : Type.
Axiom t'_inhabited : Inhabited t'.
Global Existing Instance t'_inhabited.
Axiom t'_countable : Countable t'.
Global Existing Instance t'_countable.
Program Fixpoint mon (x : list Z) (y : Z -> t) : t :=
match x with | [] => one | cons x1 r => infix_as (y x1) (mon r y) end.
Admit Obligations.
Program Fixpoint interp' (x : list m) (y : Z -> t) : t :=
match x with | [] => zero | cons (M a m1) r => infix_pl (infix_as (morph a) (mon m1 y)) (interp' r y) end.
Admit Obligations.
Definition eq_mon (m1 : list Z) (m2 : list Z) := ∀(y : Z -> t), mon m1 y = mon m2 y.
Definition eq' (x1 : list m) (x2 : list m) := ∀(y : Z -> t), interp' x1 y = interp' x2 y.
Definition append_mon (m1 : m) (m2 : m) : m := match (m1, m2) with | (M a1 l1, M a2 l2) => M (infix_as' a1 a2) (l1 ++ l2) end.
Axiom append_mon'spec : forall  (m1 : m) (m2 : m) (y : Z -> t), interp' (cons (append_mon m1 m2) ([] : list m)) y = infix_as (interp' (cons m1 ([] : list m)) y) (interp' (cons m2 ([] : list m)) y).
Program Fixpoint mul_mon (x : list m) (mon1 : m) : list m :=
match x with | [] => ([] : list m) | cons m1 r => cons (append_mon m1 mon1) (mul_mon r mon1) end.
Admit Obligations.
Axiom mul_mon'spec : forall  (x : list m) (mon1 : m) (y : Z -> t), interp' (mul_mon x mon1) y = infix_as (interp' x y) (interp' (cons mon1 ([] : list m)) y).
Program Fixpoint mul_devel (x1 : list m) (x2 : list m) : list m :=
match x1 with | [] => ([] : list m) | cons (M a m1) r => mul_mon x2 (M a m1) ++ mul_devel r x2 end.
Admit Obligations.
Axiom mul_devel'spec : forall  (x1 : list m) (x2 : list m) (y : Z -> t), interp' (mul_devel x1 x2) y = infix_as (interp' x1 y) (interp' x2 y).
Program Fixpoint conv (x : t2) : list m :=
match x with | Var v => cons (M one1 (cons v ([] : list Z))) ([] : list m) | Add x1 x2 => conv x1 ++ conv x2 | Mul x1 x2 => mul_devel (conv x1) (conv x2) | Cst n => cons (M n ([] : list Z)) ([] : list m) end.
Admit Obligations.
Axiom conv'spec : forall  (x : t2) (y : Z -> t), interp x y = interp' (conv x) y.
Program Fixpoint insert (x : Z) (l : list Z) : list Z :=
match l with | [] => cons x ([] : list Z) | cons y r => (if decide (x ≤ y) then cons x l else cons y (insert x r)) end.
Admit Obligations.
Axiom insert'spec : forall  (x : Z) (l : list Z), eq_mon (cons x l) (insert x l).
Program Fixpoint insertion_sort (l : list Z) : list Z :=
match l with | [] => ([] : list Z) | cons x r => insert x (insertion_sort r) end.
Admit Obligations.
Axiom insertion_sort'spec : forall  (l : list Z), eq_mon l (insertion_sort l).
Definition sort_mon (x : m) : m := match x with | M a m1 => M a (insertion_sort m1) end.
Axiom sort_mon'spec : forall  (x : m), eq' (cons x ([] : list m)) (cons (sort_mon x) ([] : list m)).
Program Fixpoint sort_mons (x : list m) : list m :=
match x with | [] => ([] : list m) | cons m1 r => cons (sort_mon m1) (sort_mons r) end.
Admit Obligations.
Axiom sort_mons'spec : forall  (x : list m), eq' (sort_mons x) x.
Program Fixpoint le_mon (x1 : list Z) (x2 : list Z) : bool :=
match (x1, x2) with | ([], _) => (if decide (Z.of_nat (length x1) < Z.of_nat (length x2)) then true else if decide (length x1 = length x2) then true else false) | (_, []) => (if decide (Z.of_nat (length x1) < Z.of_nat (length x2)) then true else false) | (cons v1 r1, cons v2 r2) => (if decide (Z.of_nat (length x1) < Z.of_nat (length x2)) then true else if decide (length x1 = length x2) then if decide (v1 < v2) then true else if decide (v1 = v2) then le_mon r1 r2 else false else false) end.
Admit Obligations.
Program Fixpoint same (l1 : list Z) (l2 : list Z) : bool :=
match (l1, l2) with | ([], []) => true | ([], _) => false | (_, []) => false | (cons x1 l11, cons x2 l21) => (if decide (x1 = x2) then same l11 l21 else false) end.
Admit Obligations.
Axiom same'spec : forall  (l1 : list Z) (l2 : list Z) (fact0 : same l1 l2 = true), eq_mon l1 l2.
Program Fixpoint insert_mon (m1 : m) (x : list m) : list m :=
match (m1, x) with | (_, []) => cons m1 ([] : list m) | (M a1 l1, cons (M a2 l2) r) => (if decide (same l1 l2 = true) then let s : t1 := infix_pl' a1 a2 in if decide (eq0 s) then r else cons (M s l1) r else if decide (le_mon l1 l2 = true) then cons m1 x else cons (M a2 l2) (insert_mon m1 r)) end.
Admit Obligations.
Axiom insert_mon'spec : forall  (m1 : m) (x : list m), eq' (insert_mon m1 x) (cons m1 x).
Program Fixpoint insertion_sort_mon (x : list m) : list m :=
match x with | [] => ([] : list m) | cons m1 r => insert_mon m1 (insertion_sort_mon r) end.
Admit Obligations.
Axiom insertion_sort_mon'spec : forall  (x : list m), eq' (insertion_sort_mon x) x.
Definition normalize (x : list m) : list m := insertion_sort_mon (sort_mons x).
Axiom normalize'spec : forall  (x : list m), eq' (normalize x) x.
