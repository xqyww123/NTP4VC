theory find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_bool_value_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.Compound_Compound" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_2) in i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_3 :: int). i_1 \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> t_1 (shift a i_3) = (0 :: int)) \<longrightarrow> x = (0 :: int) \<or> x = (1 :: int)"
  sorry
end
