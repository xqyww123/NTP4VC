theory X__parse_open_mode_Why3_ide_VC__parse_open_mode_loop_term_positive_part1_goal23
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.A_Length_A_Length"
begin
theorem goal23:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = l_length t_1 a_1; x_2 :: int = offset a_1; x_3 :: int = offset a in t_1 a = (43 :: int) \<longrightarrow> x = base a \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a (shift a_1 x_1) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_2 < x_3 \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> x_3 \<le> x_2 + x_1"
  sorry
end
