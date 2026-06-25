theory imp_SymbolicInterpreter_union_emptyqtvc
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
definition results_extend :: "sym_state \<Rightarrow> sym_state fset \<Rightarrow> sym_state fset \<Rightarrow> sym_state fset \<Rightarrow> _"
  where "results_extend s normals unbounds limits \<longleftrightarrow> (\<forall>(s' :: sym_state). s' |\<in>| normals \<or> s' |\<in>| unbounds \<or> s' |\<in>| limits \<longrightarrow> state_extends s s')" for s normals unbounds limits
theorem union_empty'vc:
  fixes s :: "'a fset"
  shows "s |\<union>| (fempty :: 'a fset) = s"
  sorry
end
