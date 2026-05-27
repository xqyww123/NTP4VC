theory strrchr_Why3_ide_VCstrrchr_contains_post_2_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal18:
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = base a_1; x_2 :: int = t_1 (shift a_2 i_2); x_3 :: int = offset a_2; x_4 :: int = offset a_1; x_5 :: int = l_length t_1 a_2; x_6 :: int = t_1 a; a_3 :: addr = shift a_2 x_5; a_4 :: addr = shift a_2 i_3; x_7 :: int = t_1 a_4 in t_1 a_1 = (0 :: int) \<longrightarrow> x = x_1 \<longrightarrow> x_2 = to_sint8 i_4 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> x_3 \<le> x_4 \<longrightarrow> i_2 < x_5 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_4 \<le> x_3 + x_5 \<longrightarrow> -(128 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_4 \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> is_sint8 x_6 \<longrightarrow> p_length_of_str_is t t_1 a_2 i \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> x_6 = i_4) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> (\<forall>(i_5 :: int). let x_8 :: int = i_5 + x_3 in offset a < x_8 \<longrightarrow> x_8 < x_4 \<longrightarrow> \<not>t_1 (shift a_2 i_5) = i_4)) \<longrightarrow> ((\<forall>(i_5 :: int). \<not>x_2 = t_1 (shift a_2 i_5) \<and> (0 :: int) \<le> i_5 \<and> i_5 + x_3 < x_4) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> (x_7 = x_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_3 < x_4 \<longrightarrow> (\<forall>(i_5 :: int). \<not>x_7 = x_2 \<and> i_3 < i_5 \<and> i_5 + x_3 < x_4) \<longrightarrow> a_4 = a) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a \<or> x_1 = base a \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a \<or> addr_le a_2 a \<and> addr_le a a_3 \<longrightarrow> x_2 = x_6"
  sorry
end
