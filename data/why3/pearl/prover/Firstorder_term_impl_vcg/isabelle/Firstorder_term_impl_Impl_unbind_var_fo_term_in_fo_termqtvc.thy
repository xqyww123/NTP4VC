theory Firstorder_term_impl_Impl_unbind_var_fo_term_in_fo_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Logic"
begin
theorem unbind_var_fo_term_in_fo_term'vc:
  fixes i :: "int"
  fixes t :: "(int, int) nl_fo_term"
  fixes x :: "(int, int) nl_fo_term"
  fixes bnd13 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes fr3 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes bnd10 :: "int \<Rightarrow> 'b0 symbol"
  fixes fr0 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd20 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd23 :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "correct_indexes_fo_term t"
  assumes fact2: "bound_depth_of_fo_term_in_fo_term t \<le> i + (1 :: int)"
  assumes fact3: "correct_indexes_fo_term x"
  assumes fact4: "bound_depth_of_symbol_in_fo_term x = (0 :: int)"
  assumes fact5: "bound_depth_of_fo_term_in_fo_term x = (0 :: int)"
  shows "case t of NLFVar_fo_term v0 \<Rightarrow> True | NLBruijn_fo_term v0 \<Rightarrow> True | NL_App v0 v1 \<Rightarrow> (let o1 :: int = i + (0 :: int) in ((0 :: int) \<le> nlsize_fo_term t \<and> nlsize_fo_term_list v1 < nlsize_fo_term t) \<and> (0 :: int) \<le> o1 \<and> correct_indexes_fo_term_list v1 \<and> bound_depth_of_fo_term_in_fo_term_list v1 \<le> o1 + (1 :: int) \<and> correct_indexes_fo_term x \<and> bound_depth_of_symbol_in_fo_term x = (0 :: int) \<and> bound_depth_of_fo_term_in_fo_term x = (0 :: int))"
  and "\<forall>(result :: (int, int) nl_fo_term). (case t of NLFVar_fo_term v0 \<Rightarrow> result = NLFVar_fo_term v0 | NLBruijn_fo_term v0 \<Rightarrow> (if v0 = i then result = x else result = NLBruijn_fo_term v0) | NL_App v0 v1 \<Rightarrow> (let o1 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term bnd13 identity identity; o2 :: int \<Rightarrow> ('b0, 'b3) fo_term = rename_subst_fo_term fr3 identity identity; o3 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol bnd10 identity; o4 :: int \<Rightarrow> 'b0 symbol = rename_subst_symbol fr0 identity; o5 :: int = i + (0 :: int) in \<exists>(o6 :: (int, int) nl_fo_term_list). (correct_indexes_fo_term_list o6 \<and> bound_depth_of_fo_term_in_fo_term_list o6 \<le> o5 \<and> bound_depth_of_symbol_in_fo_term_list o6 = bound_depth_of_symbol_in_fo_term_list v1 \<and> nlmodel_fo_term_list o6 o4 o3 o2 o1 = nlmodel_fo_term_list v1 o4 o3 o2 (update o1 o5 (nlmodel_fo_term x o4 (rename_subst_symbol bnd20 identity) o2 (rename_subst_fo_term bnd23 identity identity)))) \<and> result = NL_App v0 o6)) \<longrightarrow> correct_indexes_fo_term result \<and> bound_depth_of_fo_term_in_fo_term result \<le> i \<and> bound_depth_of_symbol_in_fo_term result = bound_depth_of_symbol_in_fo_term t \<and> nlmodel_fo_term result fr0 bnd10 fr3 bnd13 = nlmodel_fo_term t fr0 bnd10 fr3 (update bnd13 i (nlmodel_fo_term x fr0 bnd20 fr3 bnd23))"
  sorry
end
