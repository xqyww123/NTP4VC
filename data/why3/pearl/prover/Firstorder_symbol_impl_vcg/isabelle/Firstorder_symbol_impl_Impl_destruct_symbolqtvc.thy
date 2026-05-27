theory Firstorder_symbol_impl_Impl_destruct_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Logic"
begin
theorem destruct_symbol'vc:
  fixes t :: "nlimpl_symbol"
  assumes fact0: "nlimpl_symbol_ok t"
  shows "let o1 :: int nl_symbol = nlrepr_symbol_field t in (case o1 of NLFVar_symbol v0 \<Rightarrow> True | NLBruijn_symbol v0 \<Rightarrow> False) \<and> (\<forall>(result :: int). let result1 :: cons_symbol = NLCVar_symbol result in (case o1 of NLFVar_symbol v0 \<Rightarrow> result = v0 | NLBruijn_symbol v0 \<Rightarrow> False) \<longrightarrow> cons_ok_symbol result1 \<and> cons_rel_symbol result1 t \<and> cons_open_rel_symbol result1 t)"
  sorry
end
