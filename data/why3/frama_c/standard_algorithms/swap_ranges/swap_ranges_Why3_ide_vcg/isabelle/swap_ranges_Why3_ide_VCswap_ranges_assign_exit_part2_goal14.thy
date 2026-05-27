theory swap_ranges_Why3_ide_VCswap_ranges_assign_exit_part2_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_swap_ranges_lib.Compound_Compound" "frama_c_standard_algorithms_swap_ranges_lib.Axiomatic_Axiomatic"
begin
theorem goal14:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a i_1; a_4 :: addr = shift a_1 (0 :: int); a_5 :: addr = shift a_1 i_1; a_6 :: addr \<Rightarrow> int = havoc t_2 (havoc t_1 t_3 a_2 i) a_4 i in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_4 i \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> separated a_4 i a_2 i \<longrightarrow> p_equalranges_1' a_6 t_3 a i_1 a_1 \<longrightarrow> p_equalranges_1' a_6 t_3 a_1 i_1 a \<longrightarrow> p_unchanged_1' a_6 t_3 a i_1 i \<longrightarrow> p_unchanged_1' a_6 t_3 a_1 i_1 i \<longrightarrow> (\<not>invalid t a_3 (1 :: int) \<longrightarrow> included a_3 (1 :: int) a_2 i \<or> included a_3 (1 :: int) a_4 i) \<and> (\<not>invalid t a_5 (1 :: int) \<longrightarrow> included a_5 (1 :: int) a_2 i \<or> included a_5 (1 :: int) a_4 i)"
  sorry
end
