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
Inductive datatype :=
  | Tint : datatype
  | Tbool : datatype.
Axiom datatype_inhabited : Inhabited datatype.
Global Existing Instance datatype_inhabited.
Axiom datatype_countable : Countable datatype.
Global Existing Instance datatype_countable.
Inductive operator :=
  | Oplus : operator
  | Ominus : operator
  | Omult : operator
  | Ole : operator.
Axiom operator_inhabited : Inhabited operator.
Global Existing Instance operator_inhabited.
Axiom operator_countable : Countable operator.
Global Existing Instance operator_countable.
Axiom ident : Type.
Axiom ident_inhabited : Inhabited ident.
Global Existing Instance ident_inhabited.
Axiom ident_countable : Countable ident.
Global Existing Instance ident_countable.
Inductive term :=
  | Tconst : Z -> term
  | Tvar : Z -> term
  | Tderef : Z -> term
  | Tbin : term -> operator -> term -> term.
Axiom term_inhabited : Inhabited term.
Global Existing Instance term_inhabited.
Axiom term_countable : Countable term.
Global Existing Instance term_countable.
Inductive fmla :=
  | Fterm : term -> fmla
  | Fand : fmla -> fmla -> fmla
  | Fnot : fmla -> fmla
  | Fimplies : fmla -> fmla -> fmla
  | Flet : Z -> term -> fmla -> fmla
  | Fforall : Z -> datatype -> fmla -> fmla.
Axiom fmla_inhabited : Inhabited fmla.
Global Existing Instance fmla_inhabited.
Axiom fmla_countable : Countable fmla.
Global Existing Instance fmla_countable.
Inductive value :=
  | Vint : Z -> value
  | Vbool : bool -> value.
Axiom value_inhabited : Inhabited value.
Global Existing Instance value_inhabited.
Axiom value_countable : Countable value.
Global Existing Instance value_countable.
Axiom env : Type.
Axiom env_inhabited : Inhabited env.
Global Existing Instance env_inhabited.
Axiom env_countable : Countable env.
Global Existing Instance env_countable.
Definition eval_bin (x : value) (op : operator) (y : value) : value := match (x, y) with | (Vint x1, Vint y1) => (match op with | Oplus => Vint (x1 + y1) | Ominus => Vint (x1 - y1) | Omult => Vint (x1 * y1) | Ole => Vbool (if decide (x1 ≤ y1) then true else false) end) | (_, _) => Vbool false end.
Program Fixpoint eval_term (sigma : Z -> value) (pi : Z -> value) (t : term) : value :=
match t with | Tconst n => Vint n | Tvar id1 => pi id1 | Tderef id1 => sigma id1 | Tbin t1 op t2 => eval_bin (eval_term sigma pi t1) op (eval_term sigma pi t2) end.
Admit Obligations.
Program Fixpoint eval_fmla (sigma : Z -> value) (pi : Z -> value) (f : fmla) : Prop :=
match f with | Fterm t => eval_term sigma pi t = Vbool true | Fand f1 f2 => eval_fmla sigma pi f1 ∧ eval_fmla sigma pi f2 | Fnot f1 => ¬ eval_fmla sigma pi f1 | Fimplies f1 f2 => eval_fmla sigma pi f1 -> eval_fmla sigma pi f2 | Flet x t f1 => eval_fmla sigma (fun_updt pi x (eval_term sigma pi t)) f1 | Fforall x Tint f1 => (∀(n : Z), eval_fmla sigma (fun_updt pi x (Vint n)) f1) | Fforall x Tbool f1 => (∀(b : bool), eval_fmla sigma (fun_updt pi x (Vbool b)) f1) end.
Admit Obligations.
Program Fixpoint subst_term (e : term) (r : Z) (v : Z) : term :=
match e with | Tconst _ => e | Tvar _ => e | Tderef x => (if decide (r = x) then Tvar v else e) | Tbin e1 op e2 => Tbin (subst_term e1 r v) op (subst_term e2 r v) end.
Admit Obligations.
Program Fixpoint fresh_in_term (id1 : Z) (t : term) : Prop :=
match t with | Tconst _ => True | Tvar v => ¬ id1 = v | Tderef _ => True | Tbin t1 _ t2 => fresh_in_term id1 t1 ∧ fresh_in_term id1 t2 end.
Admit Obligations.
Program Fixpoint fresh_in_fmla (id1 : Z) (f : fmla) : Prop :=
match f with | Fterm e => fresh_in_term id1 e | Fand f1 f2 => fresh_in_fmla id1 f1 ∧ fresh_in_fmla id1 f2 | Fimplies f1 f2 => fresh_in_fmla id1 f1 ∧ fresh_in_fmla id1 f2 | Fnot f1 => fresh_in_fmla id1 f1 | Flet y t f1 => ¬ id1 = y ∧ fresh_in_term id1 t ∧ fresh_in_fmla id1 f1 | Fforall y _ f1 => ¬ id1 = y ∧ fresh_in_fmla id1 f1 end.
Admit Obligations.
Program Fixpoint subst (f : fmla) (x : Z) (v : Z) : fmla :=
match f with | Fterm e => Fterm (subst_term e x v) | Fand f1 f2 => Fand (subst f1 x v) (subst f2 x v) | Fnot f1 => Fnot (subst f1 x v) | Fimplies f1 f2 => Fimplies (subst f1 x v) (subst f2 x v) | Flet y t f1 => Flet y (subst_term t x v) (subst f1 x v) | Fforall y ty f1 => Fforall y ty (subst f1 x v) end.
Admit Obligations.
Inductive stmt :=
  | Sskip : stmt
  | Sassign : Z -> term -> stmt
  | Sseq : stmt -> stmt -> stmt
  | Sif : term -> stmt -> stmt -> stmt
  | Sassert : fmla -> stmt
  | Swhile : term -> fmla -> stmt -> stmt.
Axiom stmt_inhabited : Inhabited stmt.
Global Existing Instance stmt_inhabited.
Axiom stmt_countable : Countable stmt.
Global Existing Instance stmt_countable.
Inductive one_step : (Z -> value) -> (Z -> value) -> stmt -> (Z -> value) -> (Z -> value) -> stmt -> Prop :=
 | one_step_assign (sigma : Z -> value) (pi : Z -> value) (x : Z) (e : term) : one_step sigma pi (Sassign x e) (fun_updt sigma x (eval_term sigma pi e)) pi Sskip
 | one_step_seq (sigma : Z -> value) (pi : Z -> value) (i1 : stmt) (sigma' : Z -> value) (pi' : Z -> value) (i1' : stmt) (i2 : stmt) : one_step sigma pi i1 sigma' pi' i1' -> one_step sigma pi (Sseq i1 i2) sigma' pi' (Sseq i1' i2)
 | one_step_seq_skip (sigma : Z -> value) (pi : Z -> value) (i : stmt) : one_step sigma pi (Sseq Sskip i) sigma pi i
 | one_step_if_true (sigma : Z -> value) (pi : Z -> value) (e : term) (i1 : stmt) (i2 : stmt) : eval_term sigma pi e = Vbool true -> one_step sigma pi (Sif e i1 i2) sigma pi i1
 | one_step_if_false (sigma : Z -> value) (pi : Z -> value) (e : term) (i1 : stmt) (i2 : stmt) : eval_term sigma pi e = Vbool false -> one_step sigma pi (Sif e i1 i2) sigma pi i2
 | one_step_assert (sigma : Z -> value) (pi : Z -> value) (f : fmla) : eval_fmla sigma pi f -> one_step sigma pi (Sassert f) sigma pi Sskip
 | one_step_while_true (sigma : Z -> value) (pi : Z -> value) (inv : fmla) (e : term) (i : stmt) : eval_fmla sigma pi inv -> eval_term sigma pi e = Vbool true -> one_step sigma pi (Swhile e inv i) sigma pi (Sseq i (Swhile e inv i))
 | one_step_while_false (sigma : Z -> value) (pi : Z -> value) (inv : fmla) (e : term) (i : stmt) : eval_fmla sigma pi inv -> eval_term sigma pi e = Vbool false -> one_step sigma pi (Swhile e inv i) sigma pi Sskip.
Inductive many_steps : (Z -> value) -> (Z -> value) -> stmt -> (Z -> value) -> (Z -> value) -> stmt -> Z -> Prop :=
 | many_steps_refl (sigma : Z -> value) (pi : Z -> value) (i : stmt) : many_steps sigma pi i sigma pi i 0%Z
 | many_steps_trans (sigma1 : Z -> value) (pi1 : Z -> value) (i1 : stmt) (sigma2 : Z -> value) (pi2 : Z -> value) (i2 : stmt) (sigma3 : Z -> value) (pi3 : Z -> value) (i3 : stmt) (n : Z) : one_step sigma1 pi1 i1 sigma2 pi2 i2 -> many_steps sigma2 pi2 i2 sigma3 pi3 i3 n -> many_steps sigma1 pi1 i1 sigma3 pi3 i3 (n + 1%Z).
Definition valid_fmla (p : fmla) := ∀(sigma : Z -> value) (pi : Z -> value), eval_fmla sigma pi p.
Definition valid_triple (p : fmla) (i : stmt) (q : fmla) := ∀(sigma : Z -> value) (pi : Z -> value), eval_fmla sigma pi p -> (∀(sigma' : Z -> value) (pi' : Z -> value) (n : Z), many_steps sigma pi i sigma' pi' Sskip n -> eval_fmla sigma' pi' q).
