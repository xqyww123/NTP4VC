theory imp_SymbolicInterpreter_lookup_sym_stateqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_imp_lib.imp_Syntax" "pearl_imp_lib.imp_ConcreteSemantics" "pearl_imp_lib.imp_Svar" "pearl_imp_lib.imp_Constraint" "pearl_imp_lib.imp_SymState" "pearl_imp_lib.imp_FreshSvar" "pearl_imp_lib.imp_SymStateSet"
begin
theorem lookup_sym_state'vc:
  fixes s :: "sym_state"
  fixes x :: "program_var"
  shows "let o1 :: t = sigma s in (\<forall>(result :: svar). (case get o1 x of None \<Rightarrow> False | Some v \<Rightarrow> result = v) \<longrightarrow> get (sigma s) x = Some result) \<and> (get o1 x = None \<longrightarrow> get (sigma s) x = None)"
  sorry
end
