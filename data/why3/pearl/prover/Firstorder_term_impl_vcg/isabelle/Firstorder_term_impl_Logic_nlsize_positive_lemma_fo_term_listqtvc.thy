theory Firstorder_term_impl_Logic_nlsize_positive_lemma_fo_term_listqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec"
begin
fun nat_nlsize_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> Nat_Nat.nat"  and nat_nlsize_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> Nat_Nat.nat"  and nlsize_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> int"  and nlsize_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> int"
  where "nat_nlsize_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) = (let s :: Nat_Nat.nat = SNat ONat in s)"
      | "nat_nlsize_fo_term_list (NL_FOCons v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_nlsize_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_nlsize_fo_term v0) s1 in s2)" for v0 v1
      | "nat_nlsize_fo_term (NLFVar_fo_term v0) = SNat ONat" for v0
      | "nat_nlsize_fo_term (NLBruijn_fo_term v0) = SNat ONat" for v0
      | "nat_nlsize_fo_term (NL_App v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_nlsize_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_nlsize_symbol v0) s1 in s2)" for v0 v1
      | "nlsize_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) = (let s :: int = 1 :: int in s)"
      | "nlsize_fo_term_list (NL_FOCons v0 v1) = (let s :: int = 1 :: int; s1 :: int = nlsize_fo_term_list v1 + s; s2 :: int = nlsize_fo_term v0 + s1 in s2)" for v0 v1
      | "nlsize_fo_term (NLFVar_fo_term v0) = (1 :: int)" for v0
      | "nlsize_fo_term (NLBruijn_fo_term v0) = (1 :: int)" for v0
      | "nlsize_fo_term (NL_App v0 v1) = (let s :: int = 1 :: int; s1 :: int = nlsize_fo_term_list v1 + s; s2 :: int = nlsize_symbol v0 + s1 in s2)" for v0 v1
theorem nlsize_positive_lemma_fo_term_list'vc:
  fixes t :: "('b0, 'b3) nl_fo_term_list"
  shows "(0 :: int) < nlsize_fo_term_list t"
  sorry
end
