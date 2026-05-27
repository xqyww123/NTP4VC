theory find_next_bit_wrap_0_Why3_ide_VCfind_next_bit_wrap_0_above_post_3_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_7 :: "int"
  shows "let x :: int = t_1 (shift a i_5); x_1 :: int = t_1 (shift a i_6); a_1 :: addr = shift a (0 :: int); x_2 :: int = to_uint32 i_5 in \<not>t_1 (shift a i_2) = (0 :: int) \<longrightarrow> i_1 < i \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_3 < i_4 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_sint32 i_6 \<longrightarrow> is_uint8 (t_1 (shift a i_4)) \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 x_1 \<longrightarrow> valid_rd t a_1 i \<longrightarrow> (if x_2 < i then x_2 = i_4 else to_uint32 i_6 = i_7 \<and> i_1 \<le> l_size \<and> valid_rd t a_1 i_1 \<and> (if i_7 < i_1 then i_7 = i_4 else i_4 = i) \<and> ((\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 < i_1 \<longrightarrow> t_1 (shift a i_8) = (0 :: int)) \<longrightarrow> i_6 = i_1) \<and> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < i_1) \<longrightarrow> \<not>x_1 = (0 :: int)) \<and> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < i_1) \<longrightarrow> (0 :: int) \<le> i_6 \<and> i_6 < i_1) \<and> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < i_1) \<longrightarrow> (\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 < i_6 \<longrightarrow> t_1 (shift a i_8) = (0 :: int)))) \<longrightarrow> ((\<forall>(i_8 :: int). i_8 < i \<longrightarrow> i_1 \<le> i_8 \<longrightarrow> t_1 (shift a i_8) = (0 :: int)) \<longrightarrow> i_5 = i) \<longrightarrow> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> i_8 < i \<and> i_1 \<le> i_8) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> i_8 < i \<and> i_1 \<le> i_8) \<longrightarrow> i_5 < i) \<longrightarrow> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> i_8 < i \<and> i_1 \<le> i_8) \<longrightarrow> i_5 < i \<and> i_1 \<le> i_5) \<longrightarrow> ((\<exists>(i_8 :: int). \<not>t_1 (shift a i_8) = (0 :: int) \<and> i_8 < i \<and> i_1 \<le> i_8) \<longrightarrow> (\<forall>(i_8 :: int). i_1 \<le> i_8 \<longrightarrow> i_8 < i_5 \<longrightarrow> t_1 (shift a i_8) = (0 :: int))) \<longrightarrow> t_1 (shift a i_3) = (0 :: int)"
  sorry
end
