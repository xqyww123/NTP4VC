theory remove_copy_Why3_ide_VCremove_copy_loop_inv_size_established_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_remove_copy_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_remove_copy_lib.Compound_Compound" "frama_c_standard_algorithms_remove_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> separated a_2 i_1 a (1 :: int) \<longrightarrow> l_count_1' t_1 a_1 (0 :: int) (0 :: int) i = (0 :: int)"
  sorry
end
