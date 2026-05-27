theory find_next_and_bit_Why3_ide_VCfind_next_and_bit_above_post_2_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_5 :: "int"
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_5); x_1 :: int = t_1 (shift a_1 i_5); a_2 :: addr = shift a i_4; a_3 :: addr = shift a_1 i_4 in \<not>t_1 (shift a i_2) = (0 :: int) \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int) \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 (t_1 (shift a_1 i_3)) \<longrightarrow> is_uint8 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> (if i_3 < i then i_4 = i_3 \<and> to_sint32 i_4 = i_5 \<and> t_1 a_2 = (1 :: int) \<and> t_1 a_3 = (1 :: int) \<and> valid_rd t a_2 (1 :: int) \<and> valid_rd t a_3 (1 :: int) else to_sint32 i = i_5) \<longrightarrow> (\<forall>(i_6 :: int). i_1 \<le> i_6 \<longrightarrow> i_6 < i_3 \<longrightarrow> t_1 (shift a i_6) = (0 :: int) \<or> t_1 (shift a_1 i_6) = (0 :: int)) \<longrightarrow> \<not>x = (0 :: int) \<and> \<not>x_1 = (0 :: int)"
  sorry
end
