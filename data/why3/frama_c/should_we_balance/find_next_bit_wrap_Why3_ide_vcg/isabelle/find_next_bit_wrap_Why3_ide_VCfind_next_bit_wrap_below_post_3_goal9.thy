theory find_next_bit_wrap_Why3_ide_VCfind_next_bit_wrap_below_post_3_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal9:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  shows "let x :: int = t_1 (shift a i_4); a_1 :: addr = shift a (0 :: int); x_1 :: int = to_uint32 i_4 in \<not>t_1 (shift a i_2) = (0 :: int) \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> i \<le> l_size \<longrightarrow> i_1 \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint8 (t_1 (shift a i)) \<longrightarrow> is_uint8 (t_1 (shift a i_3)) \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_1 i \<longrightarrow> valid_rd t a_1 i_1 \<longrightarrow> (if x_1 < i_1 then x_1 = i_3 else i_3 = i) \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_1 \<longrightarrow> t_1 (shift a i_5) = (0 :: int)) \<longrightarrow> i_4 = i_1) \<longrightarrow> ((\<exists>(i_5 :: int). \<not>t_1 (shift a i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < i_1) \<longrightarrow> \<not>x = (0 :: int)) \<longrightarrow> ((\<exists>(i_5 :: int). \<not>t_1 (shift a i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < i_1) \<longrightarrow> (0 :: int) \<le> i_4 \<and> i_4 < i_1) \<longrightarrow> ((\<exists>(i_5 :: int). \<not>t_1 (shift a i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < i_1) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_4 \<longrightarrow> t_1 (shift a i_5) = (0 :: int))) \<longrightarrow> (\<forall>(i_5 :: int). i_5 < i \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> t_1 (shift a i_5) = (0 :: int)) \<longrightarrow> i_3 < i"
  sorry
end
