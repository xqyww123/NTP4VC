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
Require Import imp.imp.Syntax.
Open Scope Z_scope.
Axiom environment : Type.
Axiom environment_inhabited : Inhabited environment.
Global Existing Instance environment_inhabited.
Axiom environment_countable : Countable environment.
Global Existing Instance environment_countable.
Inductive expr_behaviour :=
  | Enormal : Z -> expr_behaviour
  | Eunbound_var : expr_behaviour.
Axiom expr_behaviour_inhabited : Inhabited expr_behaviour.
Global Existing Instance expr_behaviour_inhabited.
Axiom expr_behaviour_countable : Countable expr_behaviour.
Global Existing Instance expr_behaviour_countable.
Inductive eval_expr : (program_var -> option Z) -> expr -> expr_behaviour -> Prop :=
 | eval_lit (env : program_var -> option Z) (n : Z) : eval_expr env (Elit n) (Enormal n)
 | eval_var (env : program_var -> option Z) (x : program_var) (n : Z) : env x = Some n -> eval_expr env (Evar x) (Enormal n)
 | eval_var_undefined (env : program_var -> option Z) (x : program_var) : env x = None -> eval_expr env (Evar x) Eunbound_var
 | eval_sub (env : program_var -> option Z) (e1 : expr) (n1 : Z) (e2 : expr) (n2 : Z) : eval_expr env e1 (Enormal n1) -> eval_expr env e2 (Enormal n2) -> eval_expr env (Esub e1 e2) (Enormal (n1 - n2))
 | eval_sub_error1 (env : program_var -> option Z) (e1 : expr) (e2 : expr) : eval_expr env e1 Eunbound_var -> eval_expr env (Esub e1 e2) Eunbound_var
 | eval_sub_error2 (env : program_var -> option Z) (e1 : expr) (n1 : Z) (e2 : expr) : eval_expr env e1 (Enormal n1) -> eval_expr env e2 Eunbound_var -> eval_expr env (Esub e1 e2) Eunbound_var.
Program Fixpoint identifiers_in_expr (e : expr) : gset program_var :=
match e with | Elit _ => (∅ : gset program_var) | Evar v => ({[v]} : gset _) | Esub e1 e2 => identifiers_in_expr e1 ∪ identifiers_in_expr e2 end.
Admit Obligations.
Inductive behavior :=
  | Cnormal : behavior
  | Cunbound_var : behavior
  | Cloop_limit : behavior.
Axiom behavior_inhabited : Inhabited behavior.
Global Existing Instance behavior_inhabited.
Axiom behavior_countable : Countable behavior.
Global Existing Instance behavior_countable.
Axiom config : Type.
Axiom config_inhabited : Inhabited config.
Global Existing Instance config_inhabited.
Axiom config_countable : Countable config.
Global Existing Instance config_countable.
Axiom loop_limit : config -> option Z.
Axiom config'invariant : forall  (self : config), match loop_limit self with | None => True | Some n => 0%Z ≤ n end.
Definition config'eq (a : config) (b : config) := loop_limit a = loop_limit b.
Axiom config'inj : forall  (a : config) (b : config) (fact0 : config'eq a b), a = b.
Axiom no_limit_cnf : config.
Axiom no_limit_cnf'def : loop_limit no_limit_cnf = None.
Axiom mk_loop_cnf : Z -> config.
Axiom mk_loop_cnf'def : forall  (n : Z) (fact0 : 0%Z ≤ n), loop_limit (mk_loop_cnf n) = Some n.
Inductive exec_cmd : config -> (program_var -> option Z) -> cmd -> (program_var -> option Z) -> behavior -> Prop :=
 | exec_skip (cnf : config) (env : program_var -> option Z) : exec_cmd cnf env Cskip env Cnormal
 | exec_assign (env : program_var -> option Z) (e : expr) (n : Z) (cnf : config) (v : program_var) : eval_expr env e (Enormal n) -> exec_cmd cnf env (Cassign v e) (fun_updt env v (Some n)) Cnormal
 | exec_assign_error (env : program_var -> option Z) (e : expr) (cnf : config) (v : program_var) : eval_expr env e Eunbound_var -> exec_cmd cnf env (Cassign v e) env Cunbound_var
 | exec_seq (cnf : config) (env1 : program_var -> option Z) (c1 : cmd) (env2 : program_var -> option Z) (c2 : cmd) (env3 : program_var -> option Z) (bhv : behavior) : exec_cmd cnf env1 c1 env2 Cnormal -> exec_cmd cnf env2 c2 env3 bhv -> exec_cmd cnf env1 (Cseq c1 c2) env3 bhv
 | exec_seq_error (cnf : config) (env1 : program_var -> option Z) (c1 : cmd) (env2 : program_var -> option Z) (bhv : behavior) (c2 : cmd) : exec_cmd cnf env1 c1 env2 bhv -> ¬ bhv = Cnormal -> exec_cmd cnf env1 (Cseq c1 c2) env2 bhv
 | exec_if_false (env : program_var -> option Z) (e : expr) (cnf : config) (c2 : cmd) (env' : program_var -> option Z) (bhv : behavior) (c1 : cmd) : eval_expr env e (Enormal 0%Z) -> exec_cmd cnf env c2 env' bhv -> exec_cmd cnf env (Cif e c1 c2) env' bhv
 | exec_if_true (n : Z) (env : program_var -> option Z) (e : expr) (cnf : config) (c1 : cmd) (env' : program_var -> option Z) (bhv : behavior) (c2 : cmd) : ¬ n = 0%Z -> eval_expr env e (Enormal n) -> exec_cmd cnf env c1 env' bhv -> exec_cmd cnf env (Cif e c1 c2) env' bhv
 | exec_if_error (env : program_var -> option Z) (e : expr) (cnf : config) (c1 : cmd) (c2 : cmd) : eval_expr env e Eunbound_var -> exec_cmd cnf env (Cif e c1 c2) env Cunbound_var
 | exec_while1 (cnf : config) (env : program_var -> option Z) (e : expr) (c : cmd) (env' : program_var -> option Z) (bhv : behavior) : exec_while cnf 0%Z env e c env' bhv -> exec_cmd cnf env (Cwhile e c) env' bhv
with exec_while : config -> Z -> (program_var -> option Z) -> expr -> cmd -> (program_var -> option Z) -> behavior -> Prop :=
 | exec_while_overflow (cnf : config) (ctr : Z) (env : program_var -> option Z) (e : expr) (c : cmd) : (match loop_limit cnf with | None => False | Some n => n ≤ ctr end) -> exec_while cnf ctr env e c env Cloop_limit
 | exec_while_false (cnf : config) (ctr : Z) (env : program_var -> option Z) (e : expr) (c : cmd) : (match loop_limit cnf with | None => True | Some n => ctr < n end) -> eval_expr env e (Enormal 0%Z) -> exec_while cnf ctr env e c env Cnormal
 | exec_while_test_error (cnf : config) (ctr : Z) (env : program_var -> option Z) (e : expr) (c : cmd) : (match loop_limit cnf with | None => True | Some n => ctr < n end) -> eval_expr env e Eunbound_var -> exec_while cnf ctr env e c env Cunbound_var
 | exec_while_body_error (cnf : config) (ctr : Z) (env1 : program_var -> option Z) (e : expr) (v : Z) (c : cmd) (env2 : program_var -> option Z) (bhv : behavior) : (match loop_limit cnf with | None => True | Some n => ctr < n end) -> eval_expr env1 e (Enormal v) -> ¬ v = 0%Z -> exec_cmd cnf env1 c env2 bhv -> ¬ bhv = Cnormal -> exec_while cnf ctr env1 e c env2 bhv
 | exec_while_loop (cnf : config) (ctr : Z) (env1 : program_var -> option Z) (e : expr) (v : Z) (c : cmd) (env2 : program_var -> option Z) (env3 : program_var -> option Z) (bhv : behavior) : (match loop_limit cnf with | None => True | Some n => ctr < n end) -> eval_expr env1 e (Enormal v) -> ¬ v = 0%Z -> exec_cmd cnf env1 c env2 Cnormal -> exec_while cnf (ctr + 1%Z) env2 e c env3 bhv -> exec_while cnf ctr env1 e c env3 bhv.
