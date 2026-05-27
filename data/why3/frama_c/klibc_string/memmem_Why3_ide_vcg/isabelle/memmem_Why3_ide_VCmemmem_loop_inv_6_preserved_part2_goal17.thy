theory memmem_Why3_ide_VCmemmem_loop_inv_6_preserved_part2_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal17:
  fixes a_10 :: "addr"
  fixes a_11 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_5 :: "addr"
  fixes i_4 :: "int"
  fixes a_4 :: "addr"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  shows "let x :: int = base a_10; x_1 :: int = base a_11; x_2 :: int = t_1 (shift a_1 (1 :: int)); x_3 :: int = t_1 (shift a_1 (0 :: int)); x_4 :: int = to_uint32 ((1 :: int) + i_3); x_5 :: int = t_1 (shift a x_4); x_6 :: int = to_uint32 (i_2 - (2 :: int)); a_12 :: addr = shift a_10 (0 :: int); a_13 :: addr = shift a_11 (0 :: int); a_14 :: addr = shift a_6 (0 :: int); a_15 :: addr = shift a_7 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_2 = (1 :: int) \<longrightarrow> x = base a_1 \<longrightarrow> x_1 = base a \<longrightarrow> x_2 = x_3 \<longrightarrow> \<not>t_1 (shift a_5 i_4) = t_1 (shift a_4 i_4) \<longrightarrow> x_5 = x_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> i_4 < x_6 \<longrightarrow> i_5 < x_4 \<longrightarrow> i_3 \<le> to_uint32 (i - i_2) \<longrightarrow> i_2 + i_3 \<le> (2 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_2 \<longrightarrow> valid_rw t a_12 i_2 \<longrightarrow> valid_rw t a_13 i \<longrightarrow> separated a_13 i a_12 i_2 \<longrightarrow> valid_rw t a_14 x_6 \<longrightarrow> valid_rw t a_15 x_6 \<longrightarrow> separated a_15 x_6 a_14 x_6 \<longrightarrow> is_uint8 x_5 \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i_3 \<longrightarrow> (\<exists>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> (3 :: int) + i_7 \<le> i_2 \<longrightarrow> \<not>t_1 (shift a_3 ((2 :: int) + i_7 + i_6)) = t_1 (shift a_2 ((2 :: int) + i_7)))) \<longrightarrow> (\<exists>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> (3 :: int) + i_6 \<le> i_2 \<longrightarrow> \<not>t_1 (shift a_9 ((2 :: int) + i_6 + i_5)) = t_1 (shift a_8 ((2 :: int) + i_6)))"
  sorry
end
