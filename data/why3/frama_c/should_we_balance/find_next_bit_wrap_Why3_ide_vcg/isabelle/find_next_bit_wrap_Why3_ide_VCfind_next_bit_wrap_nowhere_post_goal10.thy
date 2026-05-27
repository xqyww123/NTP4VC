theory find_next_bit_wrap_Why3_ide_VCfind_next_bit_wrap_nowhere_post_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = t_1 (shift a i_3); a_1 :: addr = shift a (0 :: int); x_1 :: int = to_uint32 i_3 in i_1 < i \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_1 i \<longrightarrow> (if x_1 < i then x_1 = i_2 else to_uint32 i_4 = i_5 \<and> i_1 \<le> l_size \<and> valid_rd t a_1 i_1 \<and> (if i_5 < i_1 then i_5 = i_2 else i_2 = i) \<and> ((\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i_1 \<longrightarrow> t_1 (shift a i_6) = (0 :: int)) \<longrightarrow> i_4 = i_1) \<and> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < i_1) \<longrightarrow> \<not>t_1 (shift a i_4) = (0 :: int)) \<and> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < i_1) \<longrightarrow> (0 :: int) \<le> i_4 \<and> i_4 < i_1) \<and> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < i_1) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i_4 \<longrightarrow> t_1 (shift a i_6) = (0 :: int)))) \<longrightarrow> ((\<forall>(i_6 :: int). i_6 < i \<longrightarrow> i_1 \<le> i_6 \<longrightarrow> t_1 (shift a i_6) = (0 :: int)) \<longrightarrow> i_3 = i) \<longrightarrow> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> i_6 < i \<and> i_1 \<le> i_6) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> i_6 < i \<and> i_1 \<le> i_6) \<longrightarrow> i_3 < i) \<longrightarrow> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> i_6 < i \<and> i_1 \<le> i_6) \<longrightarrow> i_3 < i \<and> i_1 \<le> i_3) \<longrightarrow> ((\<exists>(i_6 :: int). \<not>t_1 (shift a i_6) = (0 :: int) \<and> i_6 < i \<and> i_1 \<le> i_6) \<longrightarrow> (\<forall>(i_6 :: int). i_1 \<le> i_6 \<longrightarrow> i_6 < i_3 \<longrightarrow> t_1 (shift a i_6) = (0 :: int))) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i \<longrightarrow> t_1 (shift a i_6) = (0 :: int)) \<longrightarrow> i_2 = i"
  sorry
end
