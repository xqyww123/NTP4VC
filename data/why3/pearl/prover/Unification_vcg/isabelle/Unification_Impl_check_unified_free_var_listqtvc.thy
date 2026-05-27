theory Unification_Impl_check_unified_free_var_listqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_prover_lib.Unification_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice" "pearl_prover_lib.BacktrackArray_Impl" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Firstorder_term_impl_Logic" "pearl_prover_lib.Firstorder_term_impl_Impl" "pearl_prover_lib.Unification_Logic"
begin
theorem check_unified_free_var_list'vc:
  fixes t :: "nlimpl_fo_term_list"
  fixes rhob :: "sdata t"
  fixes rho :: "unifier_subst"
  fixes x :: "int"
  assumes fact0: "nlimpl_fo_term_list_ok t"
  assumes fact1: "unifier_subst_ok rhob rho"
  assumes fact2: "\<forall>(y :: int). is_fo_term_free_var_in_fo_term_list y (model_fo_term_list_field t) \<longrightarrow> (0 :: int) \<le> y"
  shows "nlimpl_fo_term_list_ok t"
  and "\<forall>(o1 :: cons_fo_term_list). cons_ok_fo_term_list o1 \<and> cons_rel_fo_term_list o1 t \<and> cons_open_rel_fo_term_list o1 t \<longrightarrow> (case o1 of NLC_FONil \<Rightarrow> \<not>is_fo_term_free_var_in_fo_term_list x (subst_fo_term_list (model_fo_term_list_field t) subst_id_symbol (unifier rho)) | NLC_FOCons u q \<Rightarrow> (unifier_subst_ok rhob rho \<and> nlimpl_fo_term_ok u \<and> (\<forall>(y :: int). is_fo_term_free_var_in_fo_term y (model_fo_term_field u) \<longrightarrow> (0 :: int) \<le> y)) \<and> (\<not>is_fo_term_free_var_in_fo_term x (subst_fo_term (model_fo_term_field u) subst_id_symbol (unifier rho)) \<longrightarrow> (nlimpl_fo_term_list_ok q \<and> unifier_subst_ok rhob rho \<and> (\<forall>(y :: int). is_fo_term_free_var_in_fo_term_list y (model_fo_term_list_field q) \<longrightarrow> (0 :: int) \<le> y)) \<and> (\<not>is_fo_term_free_var_in_fo_term_list x (subst_fo_term_list (model_fo_term_list_field q) subst_id_symbol (unifier rho)) \<longrightarrow> \<not>is_fo_term_free_var_in_fo_term_list x (subst_fo_term_list (model_fo_term_list_field t) subst_id_symbol (unifier rho)))))"
  sorry
end
