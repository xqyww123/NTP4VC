theory blocking_semantics5_HoareLogic_many_steps_seqqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_FreshVariables"
begin
theorem many_steps_seq'vc:
  fixes sigma1 :: "mident \<Rightarrow> value"
  fixes pi1 :: "(ident \<times> value) list"
  fixes s1 :: "stmt"
  fixes s2 :: "stmt"
  fixes sigma3 :: "mident \<Rightarrow> value"
  fixes pi3 :: "(ident \<times> value) list"
  fixes n :: "int"
  assumes fact0: "many_steps sigma1 pi1 (Sseq s1 s2) sigma3 pi3 Sskip n"
  shows "\<exists>(sigma2 :: mident \<Rightarrow> value) (pi2 :: (ident \<times> value) list) (n1 :: int) (n2 :: int). many_steps sigma1 pi1 s1 sigma2 pi2 Sskip n1 \<and> many_steps sigma2 pi2 s2 sigma3 pi3 Sskip n2 \<and> n = (1 :: int) + n1 + n2"
  sorry
end
