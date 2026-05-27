theory rotate_copy_Why3_ide_VCrotate_copy_assign_exit_part1_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_copy_lib.Compound_Compound" "frama_c_standard_algorithms_rotate_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); a_4 :: addr = shift a (i_1 - i_2) in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> separated a_2 i_1 a_3 i_1 \<longrightarrow> valid_rd t a_2 i_2 \<and> valid_rw t a_4 i_2 \<and> \<not>invalid t a_4 i_2 \<and> separated a_2 i_2 a_4 (1 :: int) \<or> valid_rd t a_2 i_2 \<and> valid_rw t a_4 i_2 \<and> \<not>invalid t a_4 i_2 \<and> separated a_2 i_2 a_4 (1 :: int) \<and> p_equalranges_1' (havoc t_1 t_2 a_4 i_2) t_2 a_1 i_2 a_4 \<longrightarrow> included a_4 i_2 a_3 i_1"
  sorry
end
