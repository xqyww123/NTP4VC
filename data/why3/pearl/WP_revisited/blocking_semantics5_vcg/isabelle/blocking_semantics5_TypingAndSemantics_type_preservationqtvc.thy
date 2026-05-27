theory blocking_semantics5_TypingAndSemantics_type_preservationqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_Typing"
begin
definition compatible_env :: "(mident \<Rightarrow> value) \<Rightarrow> (mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> value) list \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> _"
  where "compatible_env sigma sigmat pi pit \<longleftrightarrow> (\<forall>(id1 :: mident). type_value (sigma id1) = sigmat id1) \<and> (\<forall>(id1 :: ident). type_value (get_stack id1 pi) = get_vartype id1 pit)" for sigma sigmat pi pit
theorem type_preservation'vc:
  fixes sigmat :: "mident \<Rightarrow> datatype"
  fixes pit :: "(ident \<times> datatype) list"
  fixes s1 :: "stmt"
  fixes sigma1 :: "mident \<Rightarrow> value"
  fixes pi1 :: "(ident \<times> value) list"
  fixes sigma2 :: "mident \<Rightarrow> value"
  fixes pi2 :: "(ident \<times> value) list"
  fixes s2 :: "stmt"
  assumes fact0: "type_stmt sigmat pit s1"
  assumes fact1: "compatible_env sigma1 sigmat pi1 pit"
  assumes fact2: "one_step sigma1 pi1 s1 sigma2 pi2 s2"
  shows "type_stmt sigmat pit s2"
  and "compatible_env sigma2 sigmat pi2 pit"
  sorry
end
