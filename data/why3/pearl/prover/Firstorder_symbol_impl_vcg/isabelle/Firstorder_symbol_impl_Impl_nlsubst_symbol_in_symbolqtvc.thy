theory Firstorder_symbol_impl_Impl_nlsubst_symbol_in_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Logic"
begin
theorem nlsubst_symbol_in_symbol'vc:
  fixes t :: "nlimpl_symbol"
  fixes u :: "nlimpl_symbol"
  fixes x :: "int"
  assumes fact0: "nlimpl_symbol_ok t"
  assumes fact1: "nlimpl_symbol_ok u"
  shows "let o1 :: int symbol = subst_symbol (model_symbol_field t) (update subst_id_symbol x (model_symbol_field u)) in (\<forall>(a :: int) (b :: int) (result :: int). (if a < b then result = b else result = a) \<longrightarrow> a \<le> result \<and> b \<le> result) \<and> (\<forall>(o2 :: int). nlfree_var_symbol_set_abstraction_symbol_field t \<le> o2 \<and> nlfree_var_symbol_set_abstraction_symbol_field u \<le> o2 \<longrightarrow> (let o3 :: int \<Rightarrow> int symbol = (const :: int symbol \<Rightarrow> int \<Rightarrow> int symbol) (Var_symbol (-(1 :: int))); o4 :: int \<Rightarrow> int symbol = subst_id_symbol; o5 :: int nl_symbol = nlrepr_symbol_field u; o6 :: int nl_symbol = nlrepr_symbol_field t in (correct_indexes_symbol o6 \<and> correct_indexes_symbol o5 \<and> bound_depth_of_symbol_in_symbol o5 = (0 :: int)) \<and> (\<forall>(o7 :: int nl_symbol). correct_indexes_symbol o7 \<and> bound_depth_of_symbol_in_symbol o7 = bound_depth_of_symbol_in_symbol o6 \<and> nlmodel_symbol o7 o4 o3 = nlmodel_symbol o6 (update o4 x (nlmodel_symbol o5 o4 ((const :: int symbol \<Rightarrow> int \<Rightarrow> int symbol) (Var_symbol (-(1 :: int)))))) o3 \<longrightarrow> nlimpl_symbol_ok (nlimpl_symbol'mk o7 o2 o1) \<and> o1 = subst_symbol (model_symbol_field t) (update subst_id_symbol x (model_symbol_field u)))))"
  sorry
end
