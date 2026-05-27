theory blocking_semantics5_HoareLogic_if_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_FreshVariables"
begin
definition valid_triple :: "fmla \<Rightarrow> stmt \<Rightarrow> fmla \<Rightarrow> _"
  where "valid_triple p s q \<longleftrightarrow> (\<forall>(sigma :: mident \<Rightarrow> value) (pi :: (ident \<times> value) list). eval_fmla sigma pi p \<longrightarrow> (\<forall>(sigma' :: mident \<Rightarrow> value) (pi' :: (ident \<times> value) list) (n :: int). many_steps sigma pi s sigma' pi' Sskip n \<longrightarrow> eval_fmla sigma' pi' q))" for p s q
definition total_valid_triple :: "fmla \<Rightarrow> stmt \<Rightarrow> fmla \<Rightarrow> _"
  where "total_valid_triple p s q \<longleftrightarrow> (\<forall>(sigma :: mident \<Rightarrow> value) (pi :: (ident \<times> value) list). eval_fmla sigma pi p \<longrightarrow> (\<exists>(sigma' :: mident \<Rightarrow> value) (pi' :: (ident \<times> value) list) (n :: int). many_steps sigma pi s sigma' pi' Sskip n \<and> eval_fmla sigma' pi' q))" for p s q
theorem if_rule'vc:
  fixes p :: "fmla"
  fixes t :: "term"
  fixes s1 :: "stmt"
  fixes q :: "fmla"
  fixes s2 :: "stmt"
  assumes fact0: "valid_triple (Fand p (Fterm t)) s1 q"
  assumes fact1: "valid_triple (Fand p (Fnot (Fterm t))) s2 q"
  shows "valid_triple p (Sif t s1 s2) q"
  sorry
end
