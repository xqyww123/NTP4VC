theory blocking_semantics5_HoareLogic_consequence_ruleqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_FreshVariables"
begin
definition valid_triple :: "fmla \<Rightarrow> stmt \<Rightarrow> fmla \<Rightarrow> _"
  where "valid_triple p s q \<longleftrightarrow> (\<forall>(sigma :: mident \<Rightarrow> value) (pi :: (ident \<times> value) list). eval_fmla sigma pi p \<longrightarrow> (\<forall>(sigma' :: mident \<Rightarrow> value) (pi' :: (ident \<times> value) list) (n :: int). many_steps sigma pi s sigma' pi' Sskip n \<longrightarrow> eval_fmla sigma' pi' q))" for p s q
definition total_valid_triple :: "fmla \<Rightarrow> stmt \<Rightarrow> fmla \<Rightarrow> _"
  where "total_valid_triple p s q \<longleftrightarrow> (\<forall>(sigma :: mident \<Rightarrow> value) (pi :: (ident \<times> value) list). eval_fmla sigma pi p \<longrightarrow> (\<exists>(sigma' :: mident \<Rightarrow> value) (pi' :: (ident \<times> value) list) (n :: int). many_steps sigma pi s sigma' pi' Sskip n \<and> eval_fmla sigma' pi' q))" for p s q
theorem consequence_rule'vc:
  fixes p' :: "fmla"
  fixes p :: "fmla"
  fixes s :: "stmt"
  fixes q :: "fmla"
  fixes q' :: "fmla"
  assumes fact0: "valid_fmla (Fimplies p' p)"
  assumes fact1: "valid_triple p s q"
  assumes fact2: "valid_fmla (Fimplies q q')"
  shows "valid_triple p' s q'"
  sorry
end
