theory imp_SymbolicInterpreter_state_extends_freshqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_imp_lib.imp_Syntax" "pearl_imp_lib.imp_ConcreteSemantics" "pearl_imp_lib.imp_Svar" "pearl_imp_lib.imp_Constraint" "pearl_imp_lib.imp_SymState" "pearl_imp_lib.imp_FreshSvar" "pearl_imp_lib.imp_SymStateSet"
begin
consts compose :: "(svar \<Rightarrow> int) \<Rightarrow> t \<Rightarrow> program_var \<Rightarrow> int option"
axiomatization where compose_def:   "compose rho sigma x = (case get sigma x of Some v \<Rightarrow> Some (rho v) | None \<Rightarrow> None)"
  for rho :: "svar \<Rightarrow> int"
  and sigma :: "t"
  and x :: "program_var"
definition state_extends :: "sym_state \<Rightarrow> sym_state \<Rightarrow> _"
  where "state_extends s s' \<longleftrightarrow> imp_Svar.to_fset (vars s) |\<subseteq>| imp_Svar.to_fset (vars s') \<and> (\<forall>(v :: svar). v |\<in>| imp_Svar.to_fset (vars s) \<longrightarrow> rho s v = rho s' v)" for s s'
consts svar_set_add :: "svar \<Rightarrow> imp_Svar.set \<Rightarrow> imp_Svar.set"
axiomatization where svar_set_add'def'0:   "imp_Svar.to_fset (svar_set_add v vs) = finsert v (imp_Svar.to_fset vs)"
  for v :: "svar"
  and vs :: "imp_Svar.set"
axiomatization where svar_set_add'def'1:   "if v |\<in>| imp_Svar.to_fset vs then fcard (imp_Svar.to_fset (svar_set_add v vs)) = fcard (imp_Svar.to_fset vs) else int (fcard (imp_Svar.to_fset (svar_set_add v vs))) = int (fcard (imp_Svar.to_fset vs)) + (1 :: int)"
  for v :: "svar"
  and vs :: "imp_Svar.set"
theorem state_extends_fresh'vc:
  fixes v :: "svar"
  fixes s :: "sym_state"
  fixes c :: "constr"
  fixes x :: "program_var"
  fixes n :: "int"
  assumes fact0: "is_fresh v (imp_Svar.to_fset (vars s))"
  assumes fact1: "vars_in_constraint c = finsert v fempty"
  shows "state_extends s (mk_sym_state (imp_Constraint.set (sigma s) x v) (Cconj (constr s) c) (svar_set_add v (vars s)) ((rho s)(v := n)))"
  sorry
end
