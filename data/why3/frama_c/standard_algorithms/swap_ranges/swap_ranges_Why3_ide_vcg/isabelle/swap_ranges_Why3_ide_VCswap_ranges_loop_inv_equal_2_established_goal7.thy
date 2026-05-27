theory swap_ranges_Why3_ide_VCswap_ranges_loop_inv_equal_2_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_swap_ranges_lib.Compound_Compound" "frama_c_standard_algorithms_swap_ranges_lib.Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> p_equalranges_1' t_1 t_1 a (0 :: int) a_1"
  sorry
end
