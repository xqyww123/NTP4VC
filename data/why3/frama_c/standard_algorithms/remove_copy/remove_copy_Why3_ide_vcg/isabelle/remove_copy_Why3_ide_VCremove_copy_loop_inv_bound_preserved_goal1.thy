theory remove_copy_Why3_ide_VCremove_copy_loop_inv_bound_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_remove_copy_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_remove_copy_lib.Compound_Compound" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes p :: "bool"
  shows "let x :: int = l_count_1' t_2 a_1 (0 :: int) i_5 i; x_1 :: int = (1 :: int) + i_5; a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a_1 i_5; a_4 :: addr = shift a (0 :: int); x_2 :: int = i_5 - x; a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_4 i_2; a_6 :: int = a_5 a_3 in i_5 \<le> i_2 \<longrightarrow> i_5 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> i_5 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> i_5 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x_1 \<longrightarrow> valid_rd t a_2 i_2 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rw t a_4 i_2 \<longrightarrow> separated a_2 i_2 a (1 :: int) \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_sint32 a_6 \<longrightarrow> \<not>p_hasvalue_1' a_5 a (0 :: int) x_2 i \<longrightarrow> p_unchanged_1' a_5 t_2 a_1 i_5 i_2 \<longrightarrow> p_unchanged_1' a_5 t_2 a x_2 i_2 \<longrightarrow> p_multisetretainrest_1' a_5 t_2 a_1 (0 :: int) i_5 a (0 :: int) x_2 i \<longrightarrow> (if a_6 = i then i_4 + l_count_1' t_2 a_1 (0 :: int) i_5 a_6 = i_5 else p = False \<and> i_3 = i_1 \<and> i_1 + x = i_5 \<and> i_3 + x = i_5 \<and> i_4 + x = x_1 \<and> i_5 \<le> (4294967294 :: int) + x \<and> valid_rw t (shift a x_2) (1 :: int)) \<longrightarrow> (0 :: int) \<le> i_4 \<and> i_4 \<le> x_1"
  sorry
end
