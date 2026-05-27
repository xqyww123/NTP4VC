theory memcmp_Why3_ide_VCmemcmp_eq_post_part1_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal9:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let x :: int = i - i_1; x_1 :: int = t_1 (shift a_5 x); x_2 :: int = t_1 (shift a_4 x); a_8 :: addr = shift a_6 (0 :: int); a_9 :: addr = shift a_7 (0 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>x_1 = x_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_8 i \<longrightarrow> valid_rw t a_9 i \<longrightarrow> separated a_9 i a_8 i \<longrightarrow> is_uint8 x_2 \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_sint32 (x_1 - x_2) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> t_1 (shift a_1 i_2) = t_1 (shift a i_2)) \<longrightarrow> \<not>(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i_1 < i \<longrightarrow> t_1 (shift a_3 i_2) = t_1 (shift a_2 i_2))"
  sorry
end
