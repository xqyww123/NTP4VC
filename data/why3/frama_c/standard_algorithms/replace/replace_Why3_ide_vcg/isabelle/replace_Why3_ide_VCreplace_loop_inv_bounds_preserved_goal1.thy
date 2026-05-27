theory replace_Why3_ide_VCreplace_loop_inv_bounds_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_replace_lib.Compound_Compound" "frama_c_standard_algorithms_replace_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let a_1 :: addr = shift a i_3; a_2 :: addr = shift a (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_2; a_4 :: int = a_3 a_1 in i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 ((1 :: int) + i_3) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 i_2 \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_unchanged_1' a_3 t_2 a i_3 i_2 \<longrightarrow> p_replace_2' a_3 t_2 a i_3 i_1 i \<longrightarrow> \<not>a_4 = i_1 \<or> valid_rw t a_1 (1 :: int) \<longrightarrow> -(1 :: int) \<le> i_3"
  sorry
end
