theory strrchr_Why3_ide_VCstrrchr_loop_inv_4_preserved_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = t_1 a; x_1 :: int = base a_1; x_2 :: int = base a; x_3 :: int = offset a_1; x_4 :: int = offset a; x_5 :: int = l_length t_1 a_1; x_6 :: int = t_1 a_2; a_3 :: addr = shift a_1 x_5; a_4 :: addr = shift a_1 i_2; x_7 :: int = t_1 a_4 in \<not>x = (0 :: int) \<longrightarrow> x_1 = x_2 \<longrightarrow> x = to_sint8 i_3 \<longrightarrow> x_3 \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> x_4 \<le> x_3 + x_5 \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_6 \<longrightarrow> is_sint8 (t_1 (Mk_addr (0 :: int) (0 :: int))) \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a a_3 \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> x_6 = i_3) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> (\<forall>(i_4 :: int). let x_8 :: int = i_4 + x_3 in offset a_2 < x_8 \<longrightarrow> x_8 < x_4 \<longrightarrow> \<not>t_1 (shift a_1 i_4) = i_3)) \<longrightarrow> ((\<forall>(i_4 :: int). \<not>t_1 (shift a_1 i_4) = x \<and> (0 :: int) \<le> i_4 \<and> i_4 + x_3 < x_4) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a_2) \<longrightarrow> (x_7 = x \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_3 < x_4 \<longrightarrow> (\<forall>(i_4 :: int). \<not>x_7 = x \<and> i_2 < i_4 \<and> i_4 + x_3 < x_4) \<longrightarrow> a_4 = a_2) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a_2 \<or> base a_2 = x_2 \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a_2 \<or> addr_le a_1 a_2 \<and> addr_le a_2 a_3 \<longrightarrow> addr_le a_1 (shift a (1 :: int))"
  sorry
end
