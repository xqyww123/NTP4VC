theory strrchr_Why3_ide_VCstrrchr_loop_inv_7_preserved_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = t_1 a; x_1 :: int = t_1 a_2; x_2 :: int = base a_1; x_3 :: int = base a; x_4 :: int = offset a_1; x_5 :: int = offset a; x_6 :: int = i_4 + x_4; x_7 :: int = offset a_2; x_8 :: int = l_length t_1 a_1; a_3 :: addr = shift a_1 x_8; a_4 :: addr = shift a_1 i_3; x_9 :: int = t_1 a_4 in \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = x \<longrightarrow> x_2 = x_3 \<longrightarrow> base a_2 = x_3 \<longrightarrow> x_4 \<le> x_5 \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> x_6 \<le> x_5 \<longrightarrow> x_7 < x_6 \<longrightarrow> x_5 \<le> x_4 + x_8 \<longrightarrow> -(128 :: int) \<le> x_1 \<longrightarrow> x_1 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 (t_1 (Mk_addr (0 :: int) (0 :: int))) \<longrightarrow> is_sint32 x_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> (x_9 = x_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_4 < x_5 \<longrightarrow> (\<forall>(i_5 :: int). \<not>x_9 = x_1 \<and> i_3 < i_5 \<and> i_5 + x_4 < x_5) \<longrightarrow> a_4 = a_2) \<longrightarrow> t_1 (shift a_1 i) = x_1 \<or> i < (0 :: int) \<or> x_5 \<le> i + x_4 \<longrightarrow> (\<forall>(i_5 :: int). let x_10 :: int = i_5 + x_4 in x_7 < x_10 \<longrightarrow> x_10 < x_5 \<longrightarrow> \<not>t_1 (shift a_1 i_5) = x_1) \<longrightarrow> \<not>t_1 (shift a_1 i_4) = x_1"
  sorry
end
