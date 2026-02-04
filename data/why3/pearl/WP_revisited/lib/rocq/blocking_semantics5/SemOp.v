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
Require Import WP_revisited.blocking_semantics5.Syntax.
Open Scope Z_scope.
Axiom env : Type.
Axiom env_inhabited : Inhabited env.
Global Existing Instance env_inhabited.
Axiom env_countable : Countable env.
Global Existing Instance env_countable.
Axiom stack : Type.
Axiom stack_inhabited : Inhabited stack.
Global Existing Instance stack_inhabited.
Axiom stack_countable : Countable stack.
Global Existing Instance stack_countable.
Program Fixpoint get_stack (i : ident) (pi : list (ident * value)) : value :=
match pi with | [] => Vvoid | cons (x, v) r => (if decide (x = i) then v else get_stack i r) end.
Admit Obligations.
Definition eval_bin (x : value) (op : operator) (y : value) : value := match (x, y) with | (Vint x1, Vint y1) => (match op with | Oplus => Vint (x1 + y1) | Ominus => Vint (x1 - y1) | Omult => Vint (x1 * y1) | Ole => Vbool (if decide (x1 ≤ y1) then true else false) end) | (_, _) => Vvoid end.
Program Fixpoint eval_term (sigma : mident -> value) (pi : list (ident * value)) (t : term) : value :=
match t with | Tvalue v => v | Tvar id1 => get_stack id1 pi | Tderef id1 => sigma id1 | Tbin t1 op t2 => eval_bin (eval_term sigma pi t1) op (eval_term sigma pi t2) end.
Admit Obligations.
Program Fixpoint eval_fmla (sigma : mident -> value) (pi : list (ident * value)) (f : fmla) : Prop :=
match f with | Fterm t => eval_term sigma pi t = Vbool true | Fand f1 f2 => eval_fmla sigma pi f1 ∧ eval_fmla sigma pi f2 | Fnot f1 => ¬ eval_fmla sigma pi f1 | Fimplies f1 f2 => eval_fmla sigma pi f1 -> eval_fmla sigma pi f2 | Flet x t f1 => eval_fmla sigma (cons (x, eval_term sigma pi t) pi) f1 | Fforall x TYint f1 => (∀(n : Z), eval_fmla sigma (cons (x, Vint n) pi) f1) | Fforall x TYbool f1 => (∀(b : bool), eval_fmla sigma (cons (x, Vbool b) pi) f1) | Fforall x TYunit f1 => eval_fmla sigma (cons (x, Vvoid) pi) f1 end.
Admit Obligations.
Definition valid_fmla (p : fmla) := ∀(sigma : mident -> value) (pi : list (ident * value)), eval_fmla sigma pi p.
Inductive one_step : (mident -> value) -> list (ident * value) -> stmt -> (mident -> value) -> list (ident * value) -> stmt -> Prop :=
 | one_step_assign (sigma' : mident -> value) (sigma : mident -> value) (x : mident) (pi : list (ident * value)) (t : term) : sigma' = fun_updt sigma x (eval_term sigma pi t) -> one_step sigma pi (Sassign x t) sigma' pi Sskip
 | one_step_seq_noskip (sigma : mident -> value) (pi : list (ident * value)) (s1 : stmt) (sigma' : mident -> value) (pi' : list (ident * value)) (s1' : stmt) (s2 : stmt) : one_step sigma pi s1 sigma' pi' s1' -> one_step sigma pi (Sseq s1 s2) sigma' pi' (Sseq s1' s2)
 | one_step_seq_skip (sigma : mident -> value) (pi : list (ident * value)) (s : stmt) : one_step sigma pi (Sseq Sskip s) sigma pi s
 | one_step_if_true (sigma : mident -> value) (pi : list (ident * value)) (t : term) (s1 : stmt) (s2 : stmt) : eval_term sigma pi t = Vbool true -> one_step sigma pi (Sif t s1 s2) sigma pi s1
 | one_step_if_false (sigma : mident -> value) (pi : list (ident * value)) (t : term) (s1 : stmt) (s2 : stmt) : eval_term sigma pi t = Vbool false -> one_step sigma pi (Sif t s1 s2) sigma pi s2
 | one_step_assert (sigma : mident -> value) (pi : list (ident * value)) (f : fmla) : eval_fmla sigma pi f -> one_step sigma pi (Sassert f) sigma pi Sskip
 | one_step_while_true (sigma : mident -> value) (pi : list (ident * value)) (inv : fmla) (cond : term) (body : stmt) : eval_fmla sigma pi inv -> eval_term sigma pi cond = Vbool true -> one_step sigma pi (Swhile cond inv body) sigma pi (Sseq body (Swhile cond inv body))
 | one_step_while_false (sigma : mident -> value) (pi : list (ident * value)) (inv : fmla) (cond : term) (body : stmt) : eval_fmla sigma pi inv -> eval_term sigma pi cond = Vbool false -> one_step sigma pi (Swhile cond inv body) sigma pi Sskip.
Inductive many_steps : (mident -> value) -> list (ident * value) -> stmt -> (mident -> value) -> list (ident * value) -> stmt -> Z -> Prop :=
 | many_steps_refl (sigma : mident -> value) (pi : list (ident * value)) (s : stmt) : many_steps sigma pi s sigma pi s 0%Z
 | many_steps_trans (sigma1 : mident -> value) (pi1 : list (ident * value)) (s1 : stmt) (sigma2 : mident -> value) (pi2 : list (ident * value)) (s2 : stmt) (sigma3 : mident -> value) (pi3 : list (ident * value)) (s3 : stmt) (n : Z) : one_step sigma1 pi1 s1 sigma2 pi2 s2 -> many_steps sigma2 pi2 s2 sigma3 pi3 s3 n -> many_steps sigma1 pi1 s1 sigma3 pi3 s3 (n + 1%Z).
Definition reductible (sigma : mident -> value) (pi : list (ident * value)) (s : stmt) := ∃(sigma' : mident -> value) (pi' : list (ident * value)) (s' : stmt), one_step sigma pi s sigma' pi' s'.
