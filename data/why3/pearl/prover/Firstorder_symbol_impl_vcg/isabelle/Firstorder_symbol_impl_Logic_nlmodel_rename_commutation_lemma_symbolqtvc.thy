theory Firstorder_symbol_impl_Logic_nlmodel_rename_commutation_lemma_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec"
begin
fun nat_nlsize_symbol :: "'b0 nl_symbol \<Rightarrow> Nat_Nat.nat"  and nlsize_symbol :: "'b0 nl_symbol \<Rightarrow> int"
  where "nat_nlsize_symbol (NLFVar_symbol v0) = SNat ONat" for v0
      | "nat_nlsize_symbol (NLBruijn_symbol v0) = SNat ONat" for v0
      | "nlsize_symbol (NLFVar_symbol v0) = (1 :: int)" for v0
      | "nlsize_symbol (NLBruijn_symbol v0) = (1 :: int)" for v0
consts shiftb_symbol :: "(int \<Rightarrow> 'b0 symbol) \<Rightarrow> int \<Rightarrow> 'b0 option symbol"
axiomatization where shiftb_symbol_definition:   "shiftb_symbol bnd i = (if i = (0 :: int) then Var_symbol (None :: 'b0 option) else rename_symbol (bnd (i - (1 :: int))) some)"
  for bnd :: "int \<Rightarrow> 'b0 symbol"
  and i :: "int"
definition nlmodel_symbol :: "'b0 nl_symbol \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> (int \<Rightarrow> 'c0 symbol) \<Rightarrow> 'c0 symbol"
  where "nlmodel_symbol t fr0 bnd0 = (case t of NLFVar_symbol v0 \<Rightarrow> fr0 v0 | NLBruijn_symbol v0 \<Rightarrow> bnd0 v0)" for t fr0 bnd0
theorem nlmodel_rename_commutation_lemma_symbol'vc:
  fixes t :: "'b0 nl_symbol"
  fixes fr0 :: "'b0 \<Rightarrow> 'c0 symbol"
  fixes s0 :: "'c0 \<Rightarrow> 'd0"
  fixes bnd0 :: "int \<Rightarrow> 'c0 symbol"
  shows "nlmodel_symbol t (rename_subst_symbol fr0 s0) (rename_subst_symbol bnd0 s0) = rename_symbol (nlmodel_symbol t fr0 bnd0) s0"
  sorry
end
