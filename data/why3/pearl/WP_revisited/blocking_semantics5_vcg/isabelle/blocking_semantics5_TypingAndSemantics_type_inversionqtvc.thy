theory blocking_semantics5_TypingAndSemantics_type_inversionqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_Typing"
begin
definition compatible_env :: "(mident \<Rightarrow> value) \<Rightarrow> (mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> value) list \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> _"
  where "compatible_env sigma sigmat pi pit \<longleftrightarrow> (\<forall>(id1 :: mident). type_value (sigma id1) = sigmat id1) \<and> (\<forall>(id1 :: ident). type_value (get_stack id1 pi) = get_vartype id1 pit)" for sigma sigmat pi pit
theorem type_inversion'vc:
  fixes v :: "value"
  shows "case type_value v of TYbool \<Rightarrow> (\<exists>(b :: bool). v = Vbool b) | TYint \<Rightarrow> (\<exists>(n :: int). v = Vint n) | TYunit \<Rightarrow> v = Vvoid"
  sorry
end
