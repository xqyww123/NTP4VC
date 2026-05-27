theory rotate_Why3_ide_VCrotate_assert_rte_unsigned_overflow_2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_lib.Compound_Compound" "frama_c_standard_algorithms_rotate_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> p_reverse_5' (havoc t_1 t_2 a_1 i_1) t_2 a (0 :: int) i_1 \<longrightarrow> i \<le> (4294967295 :: int) + i_1"
  sorry
end
