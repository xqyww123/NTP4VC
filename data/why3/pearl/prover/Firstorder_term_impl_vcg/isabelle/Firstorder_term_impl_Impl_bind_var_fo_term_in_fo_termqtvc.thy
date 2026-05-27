theory Firstorder_term_impl_Impl_bind_var_fo_term_in_fo_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Logic"
begin
theorem bind_var_fo_term_in_fo_term'vc:
  fixes t :: "(int, int) nl_fo_term"
  fixes i :: "int"
  fixes x :: "int"
  fixes bnd3 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes fr3 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes bnd0 :: "int \<Rightarrow> 'b0 symbol"
  fixes fr0 :: "int \<Rightarrow> 'b0 symbol"
  assumes fact0: "correct_indexes_fo_term t"
  assumes fact1: "bound_depth_of_fo_term_in_fo_term t \<le> i"
  shows "case t of NLFVar_fo_term v0 \<Rightarrow> True | NLBruijn_fo_term v0 \<Rightarrow> True | NL_App v0 v1 \<Rightarrow> ((0 :: int) \<le> nlsize_fo_term t \<and> nlsize_fo_term_list v1 < nlsize_fo_term t) \<and> correct_indexes_fo_term_list v1 \<and> bound_depth_of_fo_term_in_fo_term_list v1 \<le> i + (0 :: int)"
  and "\<forall>(result :: (int, int) nl_fo_term). (case t of NLFVar_fo_term v0 \<Rightarrow> (if v0 = x then result = NLBruijn_fo_term i else result = NLFVar_fo_term v0) | NLBruijn_fo_term v0 \<Rightarrow> result = NLBruijn_fo_term v0 | NL_App v0 v1 \<Rightarrow> (let o1 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term bnd3 identity identity; o2 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term fr3 identity identity; o3 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol bnd0 identity; o4 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol fr0 identity; o5 :: int = i + (0 :: int) in \<exists>(o6 :: (int, int) nl_fo_term_list). (bound_depth_of_fo_term_in_fo_term_list o6 \<le> o5 + (1 :: int) \<and> correct_indexes_fo_term_list o6 \<and> bound_depth_of_symbol_in_fo_term_list v1 = bound_depth_of_symbol_in_fo_term_list o6 \<and> nlmodel_fo_term_list o6 o4 o3 o2 o1 = nlmodel_fo_term_list v1 o4 o3 (update o2 x (o1 o5)) o1) \<and> result = NL_App v0 o6)) \<longrightarrow> bound_depth_of_fo_term_in_fo_term result \<le> i + (1 :: int) \<and> correct_indexes_fo_term result \<and> bound_depth_of_symbol_in_fo_term t = bound_depth_of_symbol_in_fo_term result \<and> nlmodel_fo_term result fr0 bnd0 fr3 bnd3 = nlmodel_fo_term t fr0 bnd0 (update fr3 x (bnd3 i)) bnd3"
  sorry
end
