theory imp_ConcreteSemantics_mk_loop_cnfqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_imp_lib.imp_Syntax"
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
axiomatization where loop_limit_def:   "loop_limit no_limit_cnf = None"
theorem mk_loop_cnf'vc:
  shows "True"
  sorry
end
