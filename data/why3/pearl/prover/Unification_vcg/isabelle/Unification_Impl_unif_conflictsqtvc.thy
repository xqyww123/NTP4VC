theory Unification_Impl_unif_conflictsqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_prover_lib.Unification_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice" "pearl_prover_lib.BacktrackArray_Impl" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Firstorder_term_impl_Logic" "pearl_prover_lib.Firstorder_term_impl_Impl" "pearl_prover_lib.Unification_Logic"
begin
theorem unif_conflicts'vc:
  fixes lv :: "int list"
  fixes rhob :: "sdata t"
  fixes rho :: "unifier_subst"
  assumes fact0: "\<forall>(x :: int). x \<in> set lv \<longrightarrow> (0 :: int) \<le> x"
  assumes fact1: "unifier_subst_ok rhob rho"
  shows "case lv of Nil \<Rightarrow> unifier_subst_ok rhob rho \<and> precede rhob rhob | Cons v0 q \<Rightarrow> (correct rhob \<and> (0 :: int) \<le> v0) \<and> (let o1 :: sdata list = table (current_timestamp rhob) v0 in list_forall (inv rhob) o1 \<longrightarrow> (list_forall sdata_inv o1 \<and> unifier_subst_ok rhob rho) \<and> (\<forall>(rhob1 :: sdata t). inv rhob1 = inv rhob \<longrightarrow> unifier_subst_ok rhob1 rho \<and> precede rhob rhob1 \<longrightarrow> ((\<forall>(x :: int). x \<in> set q \<longrightarrow> (0 :: int) \<le> x) \<and> unifier_subst_ok rhob1 rho) \<and> (\<forall>(rhob2 :: sdata t). inv rhob2 = inv rhob1 \<longrightarrow> (unifier_subst_ok rhob2 rho \<and> precede rhob1 rhob2 \<longrightarrow> unifier_subst_ok rhob2 rho \<and> precede rhob rhob2) \<and> (correct rhob2 \<and> precede rhob1 rhob2 \<longrightarrow> correct rhob2 \<and> precede rhob rhob2))))"
  sorry
end
