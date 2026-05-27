theory find_next_and_bit_Why3_ide_VCfind_next_and_bit_assert_rte_mem_access_2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_2; a_3 :: addr = shift a i_2 in t_1 a_2 = (1 :: int) \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 (t_1 a_3) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> t_1 (shift a i_3) = (0 :: int) \<or> t_1 (shift a_1 i_3) = (0 :: int)) \<longrightarrow> valid_rd t a_3 (1 :: int)"
  sorry
end
