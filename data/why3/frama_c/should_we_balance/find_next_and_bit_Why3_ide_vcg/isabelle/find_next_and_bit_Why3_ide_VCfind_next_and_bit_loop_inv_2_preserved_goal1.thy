theory find_next_and_bit_Why3_ide_VCfind_next_and_bit_loop_inv_2_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_should_we_balance_lib.A_thread_variables_properties_A_thread_variables_properties" "Why3STD.Cint_Cint" "frama_c_should_we_balance_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_2; x :: int = t_1 a_2; a_3 :: addr = shift a i_2 in i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i \<le> l_size \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_3 < to_uint32 ((1 :: int) + i_2) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> x = (0 :: int) \<or> x = (1 :: int) \<longrightarrow> x = (0 :: int) \<or> t_1 a_3 = (0 :: int) \<and> valid_rd t a_3 (1 :: int) \<longrightarrow> (\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> t_1 (shift a i_4) = (0 :: int) \<or> t_1 (shift a_1 i_4) = (0 :: int)) \<longrightarrow> t_1 (shift a i_3) = (0 :: int) \<or> t_1 (shift a_1 i_3) = (0 :: int)"
  sorry
end
