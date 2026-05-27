theory Firstorder_term_impl_Impl_subst_base_fo_term_in_fo_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Logic"
begin
theorem subst_base_fo_term_in_fo_term'vc:
  fixes t :: "(int, int) nl_fo_term"
  fixes u :: "(int, int) nl_fo_term"
  fixes x :: "int"
  fixes bnd13 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes fr3 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes bnd10 :: "int \<Rightarrow> 'b0 symbol"
  fixes fr0 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd20 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd23 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  assumes fact0: "correct_indexes_fo_term t"
  assumes fact1: "correct_indexes_fo_term u"
  assumes fact2: "bound_depth_of_symbol_in_fo_term u = (0 :: int)"
  assumes fact3: "bound_depth_of_fo_term_in_fo_term u = (0 :: int)"
  shows "case t of NLFVar_fo_term v0 \<Rightarrow> True | NLBruijn_fo_term v0 \<Rightarrow> True | NL_App v0 v1 \<Rightarrow> ((0 :: int) \<le> nlsize_fo_term t \<and> nlsize_fo_term_list v1 < nlsize_fo_term t) \<and> correct_indexes_fo_term_list v1 \<and> correct_indexes_fo_term u \<and> bound_depth_of_symbol_in_fo_term u = (0 :: int) \<and> bound_depth_of_fo_term_in_fo_term u = (0 :: int)"
  and "\<forall>(result :: (int, int) nl_fo_term). (case t of NLFVar_fo_term v0 \<Rightarrow> (if v0 = x then result = u else result = NLFVar_fo_term v0) | NLBruijn_fo_term v0 \<Rightarrow> result = NLBruijn_fo_term v0 | NL_App v0 v1 \<Rightarrow> (let o1 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term bnd13 identity identity; o2 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term fr3 identity identity; o3 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol bnd10 identity; o4 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol fr0 identity in \<exists>(o5 :: (int, int) nl_fo_term_list). (correct_indexes_fo_term_list o5 \<and> bound_depth_of_symbol_in_fo_term_list o5 = bound_depth_of_symbol_in_fo_term_list v1 \<and> bound_depth_of_fo_term_in_fo_term_list o5 = bound_depth_of_fo_term_in_fo_term_list v1 \<and> nlmodel_fo_term_list o5 o4 o3 o2 o1 = nlmodel_fo_term_list v1 o4 o3 (update o2 x (nlmodel_fo_term u o4 (rename_subst_symbol bnd20 identity) o2 (rename_subst_fo_term bnd23 identity identity))) o1) \<and> result = NL_App v0 o5)) \<longrightarrow> correct_indexes_fo_term result \<and> bound_depth_of_symbol_in_fo_term result = bound_depth_of_symbol_in_fo_term t \<and> bound_depth_of_fo_term_in_fo_term result = bound_depth_of_fo_term_in_fo_term t \<and> nlmodel_fo_term result fr0 bnd10 fr3 bnd13 = nlmodel_fo_term t fr0 bnd10 (update fr3 x (nlmodel_fo_term u fr0 bnd20 fr3 bnd23)) bnd13"
  sorry
end
