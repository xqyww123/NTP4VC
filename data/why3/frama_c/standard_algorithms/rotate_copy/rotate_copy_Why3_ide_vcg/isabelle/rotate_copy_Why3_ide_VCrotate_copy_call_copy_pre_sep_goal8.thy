theory rotate_copy_Why3_ide_VCrotate_copy_call_copy_pre_sep_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_copy_lib.Compound_Compound"
begin
theorem goal8:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> (4294967295 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> separated a_2 i_1 (shift a (i - i_1)) (1 :: int)"
  sorry
end
