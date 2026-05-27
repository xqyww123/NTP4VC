theory Firstorder_symbol_impl_Impl_subst_base_symbol_in_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Logic"
begin
theorem subst_base_symbol_in_symbol'vc:
  fixes t :: "int nl_symbol"
  fixes u :: "int nl_symbol"
  fixes x :: "int"
  fixes fr0 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd10 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd20 :: "int \<Rightarrow> 'b0 symbol"
  assumes fact0: "correct_indexes_symbol t"
  assumes fact1: "correct_indexes_symbol u"
  assumes fact2: "bound_depth_of_symbol_in_symbol u = (0 :: int)"
  shows "case t of NLFVar_symbol v0 \<Rightarrow> True | NLBruijn_symbol v0 \<Rightarrow> True"
  and "\<forall>(result :: int nl_symbol). (case t of NLFVar_symbol v0 \<Rightarrow> (if v0 = x then result = u else result = NLFVar_symbol v0) | NLBruijn_symbol v0 \<Rightarrow> result = NLBruijn_symbol v0) \<longrightarrow> correct_indexes_symbol result \<and> bound_depth_of_symbol_in_symbol result = bound_depth_of_symbol_in_symbol t \<and> nlmodel_symbol result fr0 bnd10 = nlmodel_symbol t (update fr0 x (nlmodel_symbol u fr0 bnd20)) bnd10"
  sorry
end
