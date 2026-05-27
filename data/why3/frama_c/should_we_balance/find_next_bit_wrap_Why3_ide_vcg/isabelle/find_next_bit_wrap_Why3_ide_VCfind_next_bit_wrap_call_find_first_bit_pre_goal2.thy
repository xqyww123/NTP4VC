theory find_next_bit_wrap_Why3_ide_VCfind_next_bit_wrap_call_find_first_bit_pre_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_2); a_1 :: addr = shift a (0 :: int) in i_1 < i \<longrightarrow> i \<le> l_size \<longrightarrow> i \<le> to_uint32 i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_1 i \<longrightarrow> ((\<forall>(i_3 :: int). i_3 < i \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> t_1 (shift a i_3) = (0 :: int)) \<longrightarrow> i_2 = i) \<longrightarrow> ((\<exists>(i_3 :: int). \<not>t_1 (shift a i_3) = (0 :: int) \<and> i_3 < i \<and> i_1 \<le> i_3) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_3 :: int). \<not>t_1 (shift a i_3) = (0 :: int) \<and> i_3 < i \<and> i_1 \<le> i_3) \<longrightarrow> i_2 < i) \<longrightarrow> ((\<exists>(i_3 :: int). \<not>t_1 (shift a i_3) = (0 :: int) \<and> i_3 < i \<and> i_1 \<le> i_3) \<longrightarrow> i_2 < i \<and> i_1 \<le> i_2) \<longrightarrow> ((\<exists>(i_3 :: int). \<not>t_1 (shift a i_3) = (0 :: int) \<and> i_3 < i \<and> i_1 \<le> i_3) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> t_1 (shift a i_3) = (0 :: int))) \<longrightarrow> valid_rd t a_1 i_1"
  sorry
end
