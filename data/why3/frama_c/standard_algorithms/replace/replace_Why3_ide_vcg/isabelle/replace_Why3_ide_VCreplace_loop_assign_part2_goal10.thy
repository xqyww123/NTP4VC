theory replace_Why3_ide_VCreplace_loop_assign_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_replace_lib.Compound_Compound" "frama_c_standard_algorithms_replace_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a i_2; a_2 :: addr = shift a (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_1; a_4 :: int = a_3 a_1 in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> \<not>invalid t a_1 (1 :: int) \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_unchanged_1' a_3 t_2 a i_2 i_1 \<longrightarrow> p_replace_2' a_3 t_2 a i_2 a_4 i \<longrightarrow> included a_1 (1 :: int) a_2 i_1"
  sorry
end
