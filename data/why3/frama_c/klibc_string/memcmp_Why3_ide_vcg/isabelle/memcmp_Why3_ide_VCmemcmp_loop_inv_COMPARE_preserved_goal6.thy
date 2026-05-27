theory memcmp_Why3_ide_VCmemcmp_loop_inv_COMPARE_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal6:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = i_1 - i; x_1 :: int = t_1 (shift a_3 x); x_2 :: int = t_1 (shift a_2 x); a_8 :: addr = shift a_6 (0 :: int); a_9 :: addr = shift a_7 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> x_1 = x_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> i_2 + to_uint32 (i - (1 :: int)) < i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_8 i_1 \<longrightarrow> valid_rw t a_9 i_1 \<longrightarrow> separated a_9 i_1 a_8 i_1 \<longrightarrow> is_uint8 x_2 \<longrightarrow> is_uint8 x_1 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> t_1 (shift a_1 i_3) = t_1 (shift a i_3)) \<longrightarrow> t_1 (shift a_5 i_2) = t_1 (shift a_4 i_2)"
  sorry
end
