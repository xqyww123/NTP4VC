theory Firstorder_term_impl_Logic_bound_depth_of_symbol_in_fo_term_list_nonnegativeqtvc
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
fun nlmodel_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> (int \<Rightarrow> 'c0 symbol) \<Rightarrow> ('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> (int \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0, 'c3) fo_term_list"  and nlmodel_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> (int \<Rightarrow> 'c0 symbol) \<Rightarrow> ('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> (int \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0, 'c3) fo_term"
  where "nlmodel_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) fr0 bnd0 fr3 bnd3 = (FONil :: ('c0, 'c3) fo_term_list)" for fr0 bnd0 fr3 bnd3
      | "nlmodel_fo_term_list (NL_FOCons v0 v1) fr0 bnd0 fr3 bnd3 = FOCons (nlmodel_fo_term v0 (rename_subst_symbol fr0 identity) (rename_subst_symbol bnd0 identity) (rename_subst_fo_term fr3 identity identity) (rename_subst_fo_term bnd3 identity identity)) (nlmodel_fo_term_list v1 (rename_subst_symbol fr0 identity) (rename_subst_symbol bnd0 identity) (rename_subst_fo_term fr3 identity identity) (rename_subst_fo_term bnd3 identity identity))" for v0 v1 fr0 bnd0 fr3 bnd3
      | "nlmodel_fo_term (NLFVar_fo_term v0) fr0 bnd0 fr3 bnd3 = fr3 v0" for v0 fr0 bnd0 fr3 bnd3
      | "nlmodel_fo_term (NLBruijn_fo_term v0) fr0 bnd0 fr3 bnd3 = bnd3 v0" for v0 fr0 bnd0 fr3 bnd3
      | "nlmodel_fo_term (NL_App v0 v1) fr0 bnd0 fr3 bnd3 = App (nlmodel_symbol v0 (rename_subst_symbol fr0 identity) (rename_subst_symbol bnd0 identity)) (nlmodel_fo_term_list v1 (rename_subst_symbol fr0 identity) (rename_subst_symbol bnd0 identity) (rename_subst_fo_term fr3 identity identity) (rename_subst_fo_term bnd3 identity identity))" for v0 v1 fr0 bnd0 fr3 bnd3
fun correct_indexes_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> _"  and correct_indexes_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> _"
  where "correct_indexes_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) = True"
      | "correct_indexes_fo_term_list (NL_FOCons v0 v1) = (correct_indexes_fo_term v0 \<and> correct_indexes_fo_term_list v1)" for v0 v1
      | "correct_indexes_fo_term (NLFVar_fo_term v0) = True" for v0
      | "correct_indexes_fo_term (NLBruijn_fo_term v0) = ((0 :: int) \<le> v0)" for v0
      | "correct_indexes_fo_term (NL_App v0 v1) = (correct_indexes_symbol v0 \<and> correct_indexes_fo_term_list v1)" for v0 v1
fun bound_depth_of_symbol_in_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> int"  and bound_depth_of_fo_term_in_fo_term_list :: "('b0, 'b3) nl_fo_term_list \<Rightarrow> int"  and bound_depth_of_symbol_in_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> int"  and bound_depth_of_fo_term_in_fo_term :: "('b0, 'b3) nl_fo_term \<Rightarrow> int"
  where "bound_depth_of_symbol_in_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) = (0 :: int)"
      | "bound_depth_of_symbol_in_fo_term_list (NL_FOCons v0 v1) = (let b :: int = bound_depth_of_symbol_in_fo_term v0; a :: int = b; b1 :: int = bound_depth_of_symbol_in_fo_term_list v1; a1 :: int = if b1 < a then a else b1 in a1)" for v0 v1
      | "bound_depth_of_fo_term_in_fo_term_list (NL_FONil :: ('b0, 'b3) nl_fo_term_list) = (0 :: int)"
      | "bound_depth_of_fo_term_in_fo_term_list (NL_FOCons v0 v1) = (let b :: int = bound_depth_of_fo_term_in_fo_term v0; a :: int = b; b1 :: int = bound_depth_of_fo_term_in_fo_term_list v1; a1 :: int = if b1 < a then a else b1 in a1)" for v0 v1
      | "bound_depth_of_symbol_in_fo_term (NLFVar_fo_term v0) = (0 :: int)" for v0
      | "bound_depth_of_symbol_in_fo_term (NLBruijn_fo_term v0) = (0 :: int)" for v0
      | "bound_depth_of_symbol_in_fo_term (NL_App v0 v1) = (let b :: int = bound_depth_of_symbol_in_symbol v0; a :: int = b; b1 :: int = bound_depth_of_symbol_in_fo_term_list v1; a1 :: int = if b1 < a then a else b1 in a1)" for v0 v1
      | "bound_depth_of_fo_term_in_fo_term (NLFVar_fo_term v0) = (0 :: int)" for v0
      | "bound_depth_of_fo_term_in_fo_term (NLBruijn_fo_term v0) = (1 :: int) + v0" for v0
      | "bound_depth_of_fo_term_in_fo_term (NL_App v0 v1) = (let b :: int = bound_depth_of_fo_term_in_fo_term_list v1; a :: int = b in a)" for v0 v1
theorem bound_depth_of_symbol_in_fo_term_list_nonnegative'vc:
  fixes t :: "('b0, 'b3) nl_fo_term_list"
  assumes fact0: "correct_indexes_fo_term_list t"
  shows "(0 :: int) \<le> bound_depth_of_symbol_in_fo_term_list t"
  sorry
end
