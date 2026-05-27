theory find_Why3_ide_VCfind_none_post_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_find_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1 in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>x = t_1 (shift a i_2)) \<longrightarrow> \<not>(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> \<not>x = t_1 (shift a i_2))"
  sorry
end
