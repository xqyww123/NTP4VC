theory Firstorder_symbol_impl_Impl_construct_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Logic"
begin
theorem construct_symbol'vc:
  fixes v0 :: "int"
  shows "let c :: cons_symbol = NLCVar_symbol v0 in cons_ok_symbol c \<longrightarrow> nlimpl_symbol_ok (nlimpl_symbol'mk (NLFVar_symbol v0) ((1 :: int) + v0) (Var_symbol v0)) \<and> cons_rel_symbol c (nlimpl_symbol'mk (NLFVar_symbol v0) ((1 :: int) + v0) (Var_symbol v0))"
  sorry
end
