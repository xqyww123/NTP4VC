theory find_next_bit_0_Why3_ide_VCfind_next_bit_0_nowhere_post_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_3 in i_1 \<le> i_2 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint8 (t_1 (shift a i_2)) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if i_2 < i then i_3 = i_2 \<and> to_sint32 i_3 = i_4 \<and> t_1 a_1 = (1 :: int) \<and> valid_rd t a_1 (1 :: int) else to_sint32 i = i_4) \<longrightarrow> (\<forall>(i_5 :: int). i_5 < i \<longrightarrow> i_1 \<le> i_5 \<longrightarrow> t_1 (shift a i_5) = (0 :: int)) \<longrightarrow> (\<forall>(i_5 :: int). i_1 \<le> i_5 \<longrightarrow> i_5 < i_2 \<longrightarrow> t_1 (shift a i_5) = (0 :: int)) \<longrightarrow> i_4 = i"
  sorry
end
