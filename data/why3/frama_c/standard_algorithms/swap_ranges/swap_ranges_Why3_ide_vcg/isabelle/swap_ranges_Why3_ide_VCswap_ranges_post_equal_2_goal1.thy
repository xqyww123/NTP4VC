theory swap_ranges_Why3_ide_VCswap_ranges_post_equal_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_swap_ranges_lib.Compound_Compound" "frama_c_standard_algorithms_swap_ranges_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_2 (havoc t_1 t_3 a_2 i) a_3 i in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> p_equalranges_1' a_4 t_3 a i_1 a_1 \<longrightarrow> p_equalranges_1' a_4 t_3 a_1 i_1 a \<longrightarrow> p_unchanged_1' a_4 t_3 a i_1 i \<longrightarrow> p_unchanged_1' a_4 t_3 a_1 i_1 i \<longrightarrow> p_equalranges_1' (havoc t_2 (havoc t_1 t_3 a_2 i_1) a_3 i_1) t_3 a i_1 a_1"
  sorry
end
