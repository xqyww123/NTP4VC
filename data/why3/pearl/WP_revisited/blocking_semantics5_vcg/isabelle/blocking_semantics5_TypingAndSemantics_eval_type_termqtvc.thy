theory blocking_semantics5_TypingAndSemantics_eval_type_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_Typing"
begin
definition compatible_env :: "(mident \<Rightarrow> value) \<Rightarrow> (mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> value) list \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> _"
  where "compatible_env sigma sigmat pi pit \<longleftrightarrow> (\<forall>(id1 :: mident). type_value (sigma id1) = sigmat id1) \<and> (\<forall>(id1 :: ident). type_value (get_stack id1 pi) = get_vartype id1 pit)" for sigma sigmat pi pit
theorem eval_type_term'vc:
  fixes sigma :: "mident \<Rightarrow> value"
  fixes sigmat :: "mident \<Rightarrow> datatype"
  fixes pi :: "(ident \<times> value) list"
  fixes pit :: "(ident \<times> datatype) list"
  fixes t :: "term"
  fixes ty :: "datatype"
  assumes fact0: "compatible_env sigma sigmat pi pit"
  assumes fact1: "type_term sigmat pit t ty"
  shows "type_value (eval_term sigma pi t) = ty"
  sorry
end
