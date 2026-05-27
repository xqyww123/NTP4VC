theory find_next_bit_wrap_Why3_ide_VCfind_next_bit_wrap_below_post_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_3); a_1 :: addr = shift a (0 :: int) in \<not>t_1 (shift a i_1) = (0 :: int) \<longrightarrow> i < i_2 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> i \<le> l_size \<longrightarrow> i_2 \<le> l_size \<longrightarrow> i \<le> to_uint32 i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_uint8 (t_1 (shift a i_2)) \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_1 i \<longrightarrow> valid_rd t a_1 i_2 \<longrightarrow> ((\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i \<longrightarrow> t_1 (shift a i_4) = (0 :: int)) \<longrightarrow> i_3 = i) \<longrightarrow> ((\<exists>(i_4 :: int). \<not>t_1 (shift a i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < i) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_4 :: int). \<not>t_1 (shift a i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < i) \<longrightarrow> (0 :: int) \<le> i_3 \<and> i_3 < i) \<longrightarrow> ((\<exists>(i_4 :: int). \<not>t_1 (shift a i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < i) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> t_1 (shift a i_4) = (0 :: int))) \<longrightarrow> \<not>(\<forall>(i_4 :: int). i \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> t_1 (shift a i_4) = (0 :: int))"
  sorry
end
