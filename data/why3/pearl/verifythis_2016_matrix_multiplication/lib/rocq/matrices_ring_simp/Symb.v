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
Require Import verifythis_2016_matrix_multiplication.matrices.MatrixArithmetic.
Require Import verifythis_2016_matrix_multiplication.sum_extended.Sum_extended.
Open Scope Z_scope.
Inductive mono :=
  | mono'mk : list Z -> bool -> mono.
Axiom mono_inhabited : Inhabited mono.
Global Existing Instance mono_inhabited.
Axiom mono_countable : Countable mono.
Global Existing Instance mono_countable.
Definition m_prod (x : mono) := match x with |  mono'mk a _ => a end.
Definition m_pos (x : mono) := match x with |  mono'mk _ a => a end.
Axiom l_mdl : (Z -> mat Z) -> list Z -> mat Z.
Axiom l_mdl_def : forall (f : Z -> mat Z) (l : list Z), l_mdl f l = (match l with | [] => create (- 1%Z) (- 1%Z) zerof | cons x [] => f x | cons x q => mul (f x) (l_mdl f q) end).
Axiom l_vld : (Z -> mat Z) -> Z -> Z -> list Z -> Prop.
Axiom l_vld_def : forall (f : Z -> mat Z) (r : Z) (c : Z) (l : list Z), l_vld f r c l = (match l with | [] => False | cons x [] => rows (f x) = r ∧ cols (f x) = c | cons x q => rows (f x) = r ∧ l_vld f (cols (f x)) c q end).
Definition m_mdl (f : Z -> mat Z) (m : mono) : mat Z := let m0 : mat Z := l_mdl f (m_prod m) in if decide (m_pos m = true) then m0 else opp m0.
Axiom lm_mdl : (Z -> mat Z) -> Z -> Z -> list mono -> mat Z.
Axiom lm_mdl_def : forall (f : Z -> mat Z) (r : Z) (c : Z) (l : list mono), lm_mdl f r c l = (match l with | [] => create r c zerof | cons x q => add (lm_mdl f r c q) (m_mdl f x) end).
Axiom lm_mdl_simp : (Z -> mat Z) -> Z -> Z -> list mono -> mat Z.
Axiom lm_mdl_simp_def : forall (f : Z -> mat Z) (r : Z) (c : Z) (l : list mono), lm_mdl_simp f r c l = (match l with | [] => create r c zerof | cons x [] => m_mdl f x | cons x q => add (lm_mdl_simp f r c q) (m_mdl f x) end).
Axiom lm_vld : (Z -> mat Z) -> Z -> Z -> list mono -> Prop.
Axiom lm_vld_def : forall (f : Z -> mat Z) (r : Z) (c : Z) (l : list mono), lm_vld f r c l = (match l with | [] => True | cons x q => l_vld f r c (m_prod x) ∧ lm_vld f r c q end).
Axiom l_compare : list Z -> list Z -> Z.
Axiom l_compare_def : forall (l1 : list Z) (l2 : list Z), l_compare l1 l2 = (match (l1, l2) with | ([], []) => 0%Z | ([], _) => - 1%Z | (_, []) => 1%Z | (cons x q, cons y r) => (if decide (x < y) then - 1%Z else if decide (y < x) then 1%Z else l_compare q r) end).
Definition m_lower (m1 : mono) (m2 : mono) := let cmp : Z := l_compare (m_prod m1) (m_prod m2) in cmp < 0%Z ∨ cmp = 0%Z ∧ (m_pos m1 = true -> m_pos m2 = true).
Definition m_collapse (l : list mono) (m : mono) : list mono := match l with | [] => cons m ([] : list mono) | cons x q => (if decide (¬ m_pos x = true ∧ m_pos m = true ∧ l_compare (m_prod m) (m_prod x) = 0%Z) then q else cons m l) end.
Axiom lm_collapse : list mono -> list mono -> list mono.
Axiom lm_collapse_def : forall (acc : list mono) (l : list mono), lm_collapse acc l = (match l with | [] => acc | cons x q => lm_collapse (m_collapse acc x) q end).
Axiom cat_rev : forall {α : Type} `{Inhabited α}, list α -> list α -> list α.
Axiom cat_rev_def : forall {α : Type} `{Inhabited α} (acc : list α) (l : list α), cat_rev acc l = (match l with | [] => acc | cons x q => cat_rev (cons x acc) q end).
Axiom lm_dump : mono -> list mono -> list mono -> list mono * list mono.
Axiom lm_dump_def : forall (x : mono) (acc : list mono) (l : list mono), lm_dump x acc l = (match l with | [] => (acc, ([] : list mono)) | cons y q => (if decide (m_lower x y) then (acc, l) else lm_dump x (m_collapse acc y) q) end).
Axiom lm_merge : list mono -> list mono -> list mono -> list mono.
Axiom lm_merge_def : forall (acc : list mono) (l1 : list mono) (l2 : list mono), lm_merge acc l1 l2 = (match l1 with | [] => cat_rev ([] : list mono) (lm_collapse acc l2) | cons x q => (match lm_dump x acc l2 with | (acc1, l21) => lm_merge (m_collapse acc1 x) q l21 end) end).
Axiom cat : forall {α : Type} `{Inhabited α}, list α -> list α -> list α.
Axiom cat_def : forall {α : Type} `{Inhabited α} (l1 : list α) (l2 : list α), cat l1 l2 = (match l1 with | [] => l2 | cons x q => cons x (cat q l2) end).
Definition m_mul (m1 : mono) (m2 : mono) : mono := mono'mk (cat (m_prod m1) (m_prod m2)) (if decide ((m_pos m1 = true) = (m_pos m2 = true)) then true else false).
Axiom m_distribute : mono -> list mono -> list mono.
Axiom m_distribute_def : forall (m : mono) (l : list mono), m_distribute m l = (match l with | [] => ([] : list mono) | cons x q => cons (m_mul m x) (m_distribute m q) end).
Axiom lm_distribute : list mono -> list mono -> list mono.
Axiom lm_distribute_def : forall (l1 : list mono) (l2 : list mono), lm_distribute l1 l2 = (match l1 with | [] => ([] : list mono) | cons x q => lm_merge ([] : list mono) (m_distribute x l2) (lm_distribute q l2) end).
Axiom lm_opp : list mono -> list mono.
Axiom lm_opp_def : forall (l : list mono), lm_opp l = (match l with | [] => ([] : list mono) | cons x q => lm_merge ([] : list mono) (cons (mono'mk (m_prod x) (if decide (¬ m_pos x = true) then true else false)) ([] : list mono)) (lm_opp q) end).
Axiom fc : Z -> Z -> mat Z.
Axiom fc'def : forall  (y0 : Z) (y1 : Z), fc y0 y1 = create y0 y1 zerof.
Definition empty : Z -> mat Z := fc 0%Z.
Inductive env :=
  | env'mk : (Z -> mat Z) -> Z -> env.
Axiom env_inhabited : Inhabited env.
Global Existing Instance env_inhabited.
Axiom env_countable : Countable env.
Global Existing Instance env_countable.
Definition ev_f (x : env) := match x with |  env'mk a _ => a end.
Definition ev_c (x : env) := match x with |  env'mk _ a => a end.
Inductive expr :=
  | expr'mk : list mono -> Z -> Z -> expr.
Axiom expr_inhabited : Inhabited expr.
Global Existing Instance expr_inhabited.
Axiom expr_countable : Countable expr.
Global Existing Instance expr_countable.
Definition e_body (x : expr) := match x with |  expr'mk a _ _ => a end.
Definition e_rows (x : expr) := match x with |  expr'mk _ a _ => a end.
Definition e_cols (x : expr) := match x with |  expr'mk _ _ a => a end.
Definition e_vld (env1 : env) (e : expr) := 0%Z ≤ e_rows e ∧ 0%Z ≤ e_cols e ∧ lm_vld (ev_f env1) (e_rows e) (e_cols e) (e_body e).
Definition e_mdl (env1 : env) (e : expr) : mat Z := lm_mdl_simp (ev_f env1) (e_rows e) (e_cols e) (e_body e).
Axiom extends1 : (Z -> mat Z) -> Z -> mat Z -> Z -> mat Z.
Axiom extends'def : forall  (f : Z -> mat Z) (c : Z) (v : mat Z) (n : Z), extends1 f c v n = (if decide (¬ n = c) then f n else v).
Definition symb_mat (m : mat Z) (n : Z) : expr := expr'mk (cons (mono'mk (cons n ([] : list Z)) true) ([] : list mono)) (rows m) (cols m).
Definition symb_opp (e : expr) : expr := expr'mk (lm_opp (e_body e)) (e_rows e) (e_cols e).
Definition symb_add (e1 : expr) (e2 : expr) : expr := expr'mk (lm_merge ([] : list mono) (e_body e1) (e_body e2)) (e_rows e1) (e_cols e1).
Definition symb_sub (e1 : expr) (e2 : expr) : expr := symb_add e1 (symb_opp e2).
Definition symb_mul (e1 : expr) (e2 : expr) : expr := expr'mk (lm_distribute (e_body e1) (e_body e2)) (e_rows e1) (e_cols e2).
