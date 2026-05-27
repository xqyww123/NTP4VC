theory memmem_Why3_ide_VCmemmem_loop_term_decrease_part1_goal33
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal33:
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let x :: int = base a_4; x_1 :: int = base a_5; x_2 :: int = t_1 (shift a_1 (1 :: int)); x_3 :: int = t_1 (shift a_1 (0 :: int)); x_4 :: int = t_1 (shift a (to_uint32 ((1 :: int) + i_2))); a_6 :: addr = shift a_4 (0 :: int); a_7 :: addr = shift a_5 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_1 = (1 :: int) \<longrightarrow> x = base a_1 \<longrightarrow> x_1 = base a \<longrightarrow> x_2 = x_3 \<longrightarrow> \<not>x_4 = x_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> i_2 \<le> to_uint32 (i - i_1) \<longrightarrow> i_1 + i_2 \<le> (2 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_2 \<longrightarrow> valid_rw t a_6 i_1 \<longrightarrow> valid_rw t a_7 i \<longrightarrow> separated a_7 i a_6 i_1 \<longrightarrow> is_uint8 x_4 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> (\<exists>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> (3 :: int) + i_4 \<le> i_1 \<longrightarrow> \<not>t_1 (shift a_3 ((2 :: int) + i_4 + i_3)) = t_1 (shift a_2 ((2 :: int) + i_4)))) \<longrightarrow> i_2 < to_uint32 ((2 :: int) + i_2)"
  sorry
end
