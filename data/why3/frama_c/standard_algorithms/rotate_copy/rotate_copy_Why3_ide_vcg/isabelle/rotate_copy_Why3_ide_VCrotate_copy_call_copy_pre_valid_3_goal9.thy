theory rotate_copy_Why3_ide_VCrotate_copy_call_copy_pre_valid_3_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_copy_lib.Compound_Compound" "frama_c_standard_algorithms_rotate_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); x :: int = i - i_1; a_4 :: addr = shift a x in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> (4294967295 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> separated a_2 i_1 a_4 (1 :: int) \<longrightarrow> p_equalranges_1' (havoc t_1 t_2 a_4 i_1) t_2 a_1 i_1 a_4 \<longrightarrow> valid_rd t (shift a_1 i_1) x"
  sorry
end
