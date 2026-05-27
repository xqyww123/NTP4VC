theory Firstorder_term_impl_Impl_construct_fo_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Logic"
begin
theorem construct_fo_term'vc:
  fixes c :: "cons_fo_term"
  assumes fact0: "cons_ok_fo_term c"
  shows "case c of NLCVar_fo_term v0 \<Rightarrow> True | NLC_App v0 v1 \<Rightarrow> (\<forall>(a :: int) (b :: int) (result :: int). (if a < b then result = b else result = a) \<longrightarrow> a \<le> result \<and> b \<le> result)"
  and "\<forall>(result :: nlimpl_fo_term). (case c of NLCVar_fo_term v0 \<Rightarrow> result = nlimpl_fo_term'mk (NLFVar_fo_term v0) (0 :: int) ((1 :: int) + v0) (Var_fo_term v0) | NLC_App v0 v1 \<Rightarrow> (\<exists>(o1 :: int). (nlfree_var_symbol_set_abstraction_symbol_field v0 \<le> o1 \<and> nlfree_var_symbol_set_abstraction_fo_term_list_field v1 \<le> o1) \<and> result = nlimpl_fo_term'mk (NL_App (nlrepr_symbol_field v0) (nlrepr_fo_term_list_field v1)) o1 (nlfree_var_fo_term_set_abstraction_fo_term_list_field v1) (App (rename_symbol (model_symbol_field v0) identity) (rename_fo_term_list (model_fo_term_list_field v1) identity identity)))) \<longrightarrow> nlimpl_fo_term_ok result \<and> cons_rel_fo_term c result"
  sorry
end
