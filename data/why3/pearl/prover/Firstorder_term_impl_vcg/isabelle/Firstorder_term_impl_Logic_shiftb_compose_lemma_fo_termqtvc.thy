theory Firstorder_term_impl_Logic_shiftb_compose_lemma_fo_termqtvc
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
consts shiftb_fo_term :: "(int \<Rightarrow> ('b0, 'b3) fo_term) \<Rightarrow> int \<Rightarrow> ('b0, 'b3 option) fo_term"
axiomatization where shiftb_fo_term_definition:   "shiftb_fo_term bnd i = (if i = (0 :: int) then Var_fo_term (None :: 'b3 option) else rename_fo_term (bnd (i - (1 :: int))) identity some)"
  for bnd :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  and i :: "int"
theorem shiftb_compose_lemma_fo_term'vc:
  fixes bnd :: "int \<Rightarrow> ('b0, 'b3) fo_term"
  fixes s0 :: "'b0 \<Rightarrow> 'c0 symbol"
  fixes s3 :: "'b3 \<Rightarrow> ('c0, 'c3) fo_term"
  shows "subst_compose_fo_term (shiftb_fo_term bnd) (rename_subst_symbol s0 identity) (olifts_fo_term s3) = shiftb_fo_term (subst_compose_fo_term bnd s0 s3)"
  sorry
end
