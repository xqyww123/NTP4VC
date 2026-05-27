theory imp_ConcreteSemantics_eval_expr_functionalqtvc
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
theorem eval_expr_functional'vc:
  fixes env :: "program_var \<Rightarrow> int option"
  fixes e :: "expr"
  fixes n1 :: "expr_behaviour"
  fixes n2 :: "expr_behaviour"
  assumes fact0: "eval_expr env e n1"
  assumes fact1: "eval_expr env e n2"
  shows "n1 = n2"
  sorry
end
