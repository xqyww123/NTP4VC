theory remove_copy_Why3_ide_VCremove_copy_assert_rte_mem_access_2_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_remove_copy_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_remove_copy_lib.Compound_Compound" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal15:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_1; a_4 :: addr = shift a_1 i_2; a_5 :: int = a_3 a_4; x :: int = l_count_1' t_2 a_1 (0 :: int) i_2 i; a_6 :: addr = shift a_1 (0 :: int); x_1 :: int = i_2 - x in \<not>a_5 = i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> i_2 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> i_2 \<le> (4294967294 :: int) + x \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a_6 i_1 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> separated a_6 i_1 a (1 :: int) \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_sint32 a_5 \<longrightarrow> \<not>p_hasvalue_1' a_3 a (0 :: int) x_1 i \<longrightarrow> p_unchanged_1' a_3 t_2 a_1 i_2 i_1 \<longrightarrow> p_unchanged_1' a_3 t_2 a x_1 i_1 \<longrightarrow> p_multisetretainrest_1' a_3 t_2 a_1 (0 :: int) i_2 a (0 :: int) x_1 i \<longrightarrow> valid_rw t (shift a x_1) (1 :: int)"
  sorry
end
