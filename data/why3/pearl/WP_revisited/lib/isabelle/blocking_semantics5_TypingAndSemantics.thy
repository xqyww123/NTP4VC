theory blocking_semantics5_TypingAndSemantics
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/blocking_semantics5_Syntax" "../../lib/isabelle/blocking_semantics5_SemOp" "../../lib/isabelle/blocking_semantics5_Typing"
begin
definition compatible_env :: "(mident \<Rightarrow> value) \<Rightarrow> (mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> value) list \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> _"
  where "compatible_env sigma sigmat pi pit \<longleftrightarrow> (\<forall>(id1 :: mident). type_value (sigma id1) = sigmat id1) \<and> (\<forall>(id1 :: ident). type_value (get_stack id1 pi) = get_vartype id1 pit)" for sigma sigmat pi pit
end
