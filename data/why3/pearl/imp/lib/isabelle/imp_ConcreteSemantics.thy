theory imp_ConcreteSemantics
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/imp_Syntax"
begin
typedecl  environment
datatype  expr_behaviour = Enormal "int" | Eunbound_var
inductive eval_expr :: "(program_var \<Rightarrow> int option) \<Rightarrow> expr \<Rightarrow> expr_behaviour \<Rightarrow> bool" where
   eval_lit: "eval_expr env (Elit n) (Enormal n)" for env :: "program_var \<Rightarrow> int option" and n :: "int"
 | eval_var: "env x = Some n \<Longrightarrow> eval_expr env (Evar x) (Enormal n)" for env :: "program_var \<Rightarrow> int option" and x :: "program_var" and n :: "int"
 | eval_var_undefined: "env x = None \<Longrightarrow> eval_expr env (Evar x) Eunbound_var" for env :: "program_var \<Rightarrow> int option" and x :: "program_var"
 | eval_sub: "eval_expr env e1 (Enormal n1) \<Longrightarrow> eval_expr env e2 (Enormal n2) \<Longrightarrow> eval_expr env (Esub e1 e2) (Enormal (n1 - n2))" for env :: "program_var \<Rightarrow> int option" and e1 :: "expr" and n1 :: "int" and e2 :: "expr" and n2 :: "int"
 | eval_sub_error1: "eval_expr env e1 Eunbound_var \<Longrightarrow> eval_expr env (Esub e1 e2) Eunbound_var" for env :: "program_var \<Rightarrow> int option" and e1 :: "expr" and e2 :: "expr"
 | eval_sub_error2: "eval_expr env e1 (Enormal n1) \<Longrightarrow> eval_expr env e2 Eunbound_var \<Longrightarrow> eval_expr env (Esub e1 e2) Eunbound_var" for env :: "program_var \<Rightarrow> int option" and e1 :: "expr" and n1 :: "int" and e2 :: "expr"
fun identifiers_in_expr :: "expr \<Rightarrow> program_var fset"
  where "identifiers_in_expr (Elit x) = fempty" for x
      | "identifiers_in_expr (Evar v) = finsert v fempty" for v
      | "identifiers_in_expr (Esub e1 e2) = identifiers_in_expr e1 |\<union>| identifiers_in_expr e2" for e1 e2
datatype  behavior = Cnormal | Cunbound_var | Cloop_limit
typedecl  config
consts loop_limit :: "config \<Rightarrow> int option"
axiomatization where config'invariant:   "case loop_limit self of None \<Rightarrow> True | Some n \<Rightarrow> (0 :: int) \<le> n"
  for self :: "config"
definition config'eq :: "config \<Rightarrow> config \<Rightarrow> _"
  where "config'eq a b \<longleftrightarrow> loop_limit a = loop_limit b" for a b
axiomatization where config'inj:   "a = b"
 if "config'eq a b"
  for a :: "config"
  and b :: "config"
consts no_limit_cnf :: "config"
axiomatization where no_limit_cnf'def:   "loop_limit no_limit_cnf = None"
consts mk_loop_cnf :: "int \<Rightarrow> config"
axiomatization where mk_loop_cnf'def:   "loop_limit (mk_loop_cnf n) = Some n"
 if "(0 :: int) \<le> n"
  for n :: "int"
inductive exec_cmd :: "config \<Rightarrow> (program_var \<Rightarrow> int option) \<Rightarrow> cmd \<Rightarrow> (program_var \<Rightarrow> int option) \<Rightarrow> behavior \<Rightarrow> bool" and exec_while :: "config \<Rightarrow> int \<Rightarrow> (program_var \<Rightarrow> int option) \<Rightarrow> expr \<Rightarrow> cmd \<Rightarrow> (program_var \<Rightarrow> int option) \<Rightarrow> behavior \<Rightarrow> bool" where
   exec_skip: "exec_cmd cnf env Cskip env Cnormal" for cnf :: "config" and env :: "program_var \<Rightarrow> int option"
 | exec_assign: "eval_expr env e (Enormal n) \<Longrightarrow> exec_cmd cnf env (Cassign v e) (env(v := Some n)) Cnormal" for env :: "program_var \<Rightarrow> int option" and e :: "expr" and n :: "int" and cnf :: "config" and v :: "program_var"
 | exec_assign_error: "eval_expr env e Eunbound_var \<Longrightarrow> exec_cmd cnf env (Cassign v e) env Cunbound_var" for env :: "program_var \<Rightarrow> int option" and e :: "expr" and cnf :: "config" and v :: "program_var"
 | exec_seq: "exec_cmd cnf env1 c1 env2 Cnormal \<Longrightarrow> exec_cmd cnf env2 c2 env3 bhv \<Longrightarrow> exec_cmd cnf env1 (Cseq c1 c2) env3 bhv" for cnf :: "config" and env1 :: "program_var \<Rightarrow> int option" and c1 :: "cmd" and env2 :: "program_var \<Rightarrow> int option" and c2 :: "cmd" and env3 :: "program_var \<Rightarrow> int option" and bhv :: "behavior"
 | exec_seq_error: "exec_cmd cnf env1 c1 env2 bhv \<Longrightarrow> \<not>bhv = Cnormal \<Longrightarrow> exec_cmd cnf env1 (Cseq c1 c2) env2 bhv" for cnf :: "config" and env1 :: "program_var \<Rightarrow> int option" and c1 :: "cmd" and env2 :: "program_var \<Rightarrow> int option" and bhv :: "behavior" and c2 :: "cmd"
 | exec_if_false: "eval_expr env e (Enormal (0 :: int)) \<Longrightarrow> exec_cmd cnf env c2 env' bhv \<Longrightarrow> exec_cmd cnf env (Cif e c1 c2) env' bhv" for env :: "program_var \<Rightarrow> int option" and e :: "expr" and cnf :: "config" and c2 :: "cmd" and env' :: "program_var \<Rightarrow> int option" and bhv :: "behavior" and c1 :: "cmd"
 | exec_if_true: "\<not>n = (0 :: int) \<Longrightarrow> eval_expr env e (Enormal n) \<Longrightarrow> exec_cmd cnf env c1 env' bhv \<Longrightarrow> exec_cmd cnf env (Cif e c1 c2) env' bhv" for n :: "int" and env :: "program_var \<Rightarrow> int option" and e :: "expr" and cnf :: "config" and c1 :: "cmd" and env' :: "program_var \<Rightarrow> int option" and bhv :: "behavior" and c2 :: "cmd"
 | exec_if_error: "eval_expr env e Eunbound_var \<Longrightarrow> exec_cmd cnf env (Cif e c1 c2) env Cunbound_var" for env :: "program_var \<Rightarrow> int option" and e :: "expr" and cnf :: "config" and c1 :: "cmd" and c2 :: "cmd"
 | exec_while1: "exec_while cnf (0 :: int) env e c env' bhv \<Longrightarrow> exec_cmd cnf env (Cwhile e c) env' bhv" for cnf :: "config" and env :: "program_var \<Rightarrow> int option" and e :: "expr" and c :: "cmd" and env' :: "program_var \<Rightarrow> int option" and bhv :: "behavior"
 | exec_while_overflow: "(case loop_limit cnf of None \<Rightarrow> False | Some n \<Rightarrow> n \<le> ctr) \<Longrightarrow> exec_while cnf ctr env e c env Cloop_limit" for cnf :: "config" and ctr :: "int" and env :: "program_var \<Rightarrow> int option" and e :: "expr" and c :: "cmd"
 | exec_while_false: "(case loop_limit cnf of None \<Rightarrow> True | Some n \<Rightarrow> ctr < n) \<Longrightarrow> eval_expr env e (Enormal (0 :: int)) \<Longrightarrow> exec_while cnf ctr env e c env Cnormal" for cnf :: "config" and ctr :: "int" and env :: "program_var \<Rightarrow> int option" and e :: "expr" and c :: "cmd"
 | exec_while_test_error: "(case loop_limit cnf of None \<Rightarrow> True | Some n \<Rightarrow> ctr < n) \<Longrightarrow> eval_expr env e Eunbound_var \<Longrightarrow> exec_while cnf ctr env e c env Cunbound_var" for cnf :: "config" and ctr :: "int" and env :: "program_var \<Rightarrow> int option" and e :: "expr" and c :: "cmd"
 | exec_while_body_error: "(case loop_limit cnf of None \<Rightarrow> True | Some n \<Rightarrow> ctr < n) \<Longrightarrow> eval_expr env1 e (Enormal v) \<Longrightarrow> \<not>v = (0 :: int) \<Longrightarrow> exec_cmd cnf env1 c env2 bhv \<Longrightarrow> \<not>bhv = Cnormal \<Longrightarrow> exec_while cnf ctr env1 e c env2 bhv" for cnf :: "config" and ctr :: "int" and env1 :: "program_var \<Rightarrow> int option" and e :: "expr" and v :: "int" and c :: "cmd" and env2 :: "program_var \<Rightarrow> int option" and bhv :: "behavior"
 | exec_while_loop: "(case loop_limit cnf of None \<Rightarrow> True | Some n \<Rightarrow> ctr < n) \<Longrightarrow> eval_expr env1 e (Enormal v) \<Longrightarrow> \<not>v = (0 :: int) \<Longrightarrow> exec_cmd cnf env1 c env2 Cnormal \<Longrightarrow> exec_while cnf (ctr + (1 :: int)) env2 e c env3 bhv \<Longrightarrow> exec_while cnf ctr env1 e c env3 bhv" for cnf :: "config" and ctr :: "int" and env1 :: "program_var \<Rightarrow> int option" and e :: "expr" and v :: "int" and c :: "cmd" and env2 :: "program_var \<Rightarrow> int option" and env3 :: "program_var \<Rightarrow> int option" and bhv :: "behavior"
end
