theory rotate_Why3_ide_VCrotate_assign_exit_part2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_lib.Compound_Compound" "frama_c_standard_algorithms_rotate_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i_2; a_3 :: addr = shift a i_2; x :: int = i_1 - i_2 in (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> p_reverse_5' a_2 t_3 a (0 :: int) i_2 \<longrightarrow> valid_rw t a_3 x \<and> \<not>invalid t a_3 x \<or> valid_rw t a_3 x \<and> \<not>invalid t a_3 x \<and> p_reverse_5' (havoc t_2 a_2 a_3 x) a_2 a_3 (0 :: int) x \<longrightarrow> included a_3 x a_1 i_1"
  sorry
end
