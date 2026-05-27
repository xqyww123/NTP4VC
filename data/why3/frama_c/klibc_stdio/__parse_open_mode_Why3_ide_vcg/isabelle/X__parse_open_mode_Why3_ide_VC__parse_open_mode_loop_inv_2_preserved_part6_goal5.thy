theory X__parse_open_mode_Why3_ide_VC__parse_open_mode_loop_inv_2_preserved_part6_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.A_Length_A_Length"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = offset a_1; x_2 :: int = offset a in t_1 a = (120 :: int) \<longrightarrow> x = base a \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i_2 + x_1 \<le> x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a (shift a_1 (l_length t_1 a_1)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_1 < x_2 \<longrightarrow> \<not>t_1 (shift a_1 i_3) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)"
  sorry
end
