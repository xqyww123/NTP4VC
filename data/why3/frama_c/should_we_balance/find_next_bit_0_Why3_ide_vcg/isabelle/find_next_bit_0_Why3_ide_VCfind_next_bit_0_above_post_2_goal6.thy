theory find_next_bit_0_Why3_ide_VCfind_next_bit_0_above_post_2_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_5); a_1 :: addr = shift a i_4 in \<not>t_1 (shift a i_2) = (0 :: int) \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_uint8 (t_1 (shift a i_3)) \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if i_3 < i then i_4 = i_3 \<and> to_sint32 i_4 = i_5 \<and> t_1 a_1 = (1 :: int) \<and> valid_rd t a_1 (1 :: int) else to_sint32 i = i_5) \<longrightarrow> (\<forall>(i_6 :: int). i_1 \<le> i_6 \<longrightarrow> i_6 < i_3 \<longrightarrow> t_1 (shift a i_6) = (0 :: int)) \<longrightarrow> \<not>x = (0 :: int)"
  sorry
end
