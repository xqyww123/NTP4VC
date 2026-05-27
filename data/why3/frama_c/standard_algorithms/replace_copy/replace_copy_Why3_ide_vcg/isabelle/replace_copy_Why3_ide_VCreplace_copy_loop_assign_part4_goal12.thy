theory replace_copy_Why3_ide_VCreplace_copy_loop_assign_part4_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_replace_copy_lib.Compound_Compound" "frama_c_standard_algorithms_replace_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal12:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_2; a_4 :: addr = shift a_1 i_3; a_5 :: int = a_3 a_4; a_6 :: addr = shift a_1 (0 :: int); a_7 :: addr = shift a i_3 in \<not>a_5 = i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rd t a_6 i_2 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rw t a_2 i_2 \<longrightarrow> valid_rw t a_7 (1 :: int) \<longrightarrow> \<not>invalid t a_7 (1 :: int) \<longrightarrow> separated a_6 i_2 a (1 :: int) \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_unchanged_1' a_3 t_2 a_1 i_3 i_2 \<longrightarrow> p_replace_1' a_3 t_2 a_1 i_3 a i_1 i \<longrightarrow> included a_7 (1 :: int) a_2 i_2"
  sorry
end
