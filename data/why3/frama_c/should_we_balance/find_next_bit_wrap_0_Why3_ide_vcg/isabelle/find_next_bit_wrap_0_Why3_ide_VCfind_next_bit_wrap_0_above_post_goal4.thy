theory find_next_bit_wrap_0_Why3_ide_VCfind_next_bit_wrap_0_above_post_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_6 :: "int"
  shows "let x :: int = t_1 (shift a i_4); x_1 :: int = t_1 (shift a i_5); a_1 :: addr = shift a (0 :: int); x_2 :: int = to_uint32 i_4 in \<not>t_1 (shift a i_2) = (0 :: int) \<longrightarrow> i_1 < i \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_uint8 (t_1 (shift a i_3)) \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 x_1 \<longrightarrow> valid_rd t a_1 i \<longrightarrow> (if x_2 < i then x_2 = i_3 else to_uint32 i_5 = i_6 \<and> i_1 \<le> l_size \<and> valid_rd t a_1 i_1 \<and> (if i_6 < i_1 then i_6 = i_3 else i_3 = i) \<and> ((\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_1 \<longrightarrow> t_1 (shift a i_7) = (0 :: int)) \<longrightarrow> i_5 = i_1) \<and> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < i_1) \<longrightarrow> \<not>x_1 = (0 :: int)) \<and> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < i_1) \<longrightarrow> (0 :: int) \<le> i_5 \<and> i_5 < i_1) \<and> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < i_1) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_5 \<longrightarrow> t_1 (shift a i_7) = (0 :: int)))) \<longrightarrow> ((\<forall>(i_7 :: int). i_7 < i \<longrightarrow> i_1 \<le> i_7 \<longrightarrow> t_1 (shift a i_7) = (0 :: int)) \<longrightarrow> i_4 = i) \<longrightarrow> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> i_7 < i \<and> i_1 \<le> i_7) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> i_7 < i \<and> i_1 \<le> i_7) \<longrightarrow> i_4 < i) \<longrightarrow> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> i_7 < i \<and> i_1 \<le> i_7) \<longrightarrow> i_4 < i \<and> i_1 \<le> i_4) \<longrightarrow> ((\<exists>(i_7 :: int). \<not>t_1 (shift a i_7) = (0 :: int) \<and> i_7 < i \<and> i_1 \<le> i_7) \<longrightarrow> (\<forall>(i_7 :: int). i_1 \<le> i_7 \<longrightarrow> i_7 < i_4 \<longrightarrow> t_1 (shift a i_7) = (0 :: int))) \<longrightarrow> i_3 < i \<and> i_1 \<le> i_3"
  sorry
end
