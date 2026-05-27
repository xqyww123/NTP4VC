theory imp_SymState_sym_stateqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_imp_lib.imp_Syntax" "pearl_imp_lib.imp_Svar" "pearl_imp_lib.imp_Constraint"
begin
theorem sym_state'vc:
  fixes o1 :: "imp_Svar.set"
  assumes fact0: "to_fset o1 = fempty"
  assumes fact1: "int (fcard (to_fset o1)) = (0 :: int)"
  shows "let constr :: constr = Ctrue in vars_in_constraint constr |\<subseteq>| to_fset o1 \<and> (vars_in_constraint constr |\<subseteq>| to_fset o1 \<longrightarrow> (\<forall>(x :: program_var) (v :: svar). get empty x = Some v \<longrightarrow> v |\<in>| to_fset o1))"
  sorry
end
