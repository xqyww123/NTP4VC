theory copy_Why3_ide_VCcopy_assert_rte_unsigned_overflow_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_copy_lib.Compound_Compound" "frama_c_standard_algorithms_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd t (shift a_1 i_1) (1 :: int) \<longrightarrow> valid_rw t a_3 i \<longrightarrow> valid_rw t (shift a i_1) (1 :: int) \<longrightarrow> separated a_2 i a (1 :: int) \<longrightarrow> p_equalranges_1' a_4 t_2 a_1 i_1 a \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 i_1 i \<longrightarrow> i_1 \<le> (4294967294 :: int)"
  sorry
end
