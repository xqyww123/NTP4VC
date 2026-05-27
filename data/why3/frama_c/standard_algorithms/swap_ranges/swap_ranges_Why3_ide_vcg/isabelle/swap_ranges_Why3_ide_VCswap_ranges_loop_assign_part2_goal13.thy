theory swap_ranges_Why3_ide_VCswap_ranges_loop_assign_part2_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_swap_ranges_lib.Compound_Compound" "frama_c_standard_algorithms_swap_ranges_lib.Axiomatic_Axiomatic"
begin
theorem goal13:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_2 (havoc t_1 t_3 a_2 i_1) a_3 i_1; a_5 :: addr = shift a i_2; a_6 :: addr = shift a_1 i_2; a_7 :: int = a_4 a_5; a_8 :: int = (a_4(a_6 := a_7, a_5 := i)) a_5; a_9 :: int = a_4 a_6 in a_8 = a_9 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> valid_rw t a_6 (1 :: int) \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> is_sint32 a_7 \<longrightarrow> is_sint32 a_9 \<longrightarrow> is_sint32 a_8 \<longrightarrow> p_equalranges_1' a_4 t_3 a i_2 a_1 \<longrightarrow> p_equalranges_1' a_4 t_3 a_1 i_2 a \<longrightarrow> p_unchanged_1' a_4 t_3 a i_2 i_1 \<longrightarrow> p_unchanged_1' a_4 t_3 a_1 i_2 i_1 \<longrightarrow> (\<not>invalid t a_5 (1 :: int) \<longrightarrow> included a_5 (1 :: int) a_2 i_1 \<or> included a_5 (1 :: int) a_3 i_1) \<and> (\<not>invalid t a_6 (1 :: int) \<longrightarrow> included a_6 (1 :: int) a_2 i_1 \<or> included a_6 (1 :: int) a_3 i_1)"
  sorry
end
