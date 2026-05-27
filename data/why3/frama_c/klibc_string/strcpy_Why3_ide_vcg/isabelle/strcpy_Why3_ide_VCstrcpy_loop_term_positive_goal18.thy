theory strcpy_Why3_ide_VCstrcpy_loop_term_positive_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal18:
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  shows "let x :: int = base a; a_3 :: addr = shift a_2 (0 :: int); x_1 :: int = offset a_1; x_2 :: int = offset a; x_3 :: int = x_1 - x_2; a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 x_3; a_5 :: int = a_4 a_1; x_4 :: int = l_length a_4 a; x_5 :: int = (1 :: int) + l_length t_2 a; a_6 :: addr = shift a_2 x_3 in \<not>a_2 = a \<longrightarrow> base a_1 = x \<longrightarrow> \<not>a_5 = (0 :: int) \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 + x_4 \<longrightarrow> i \<le> (2000 :: int) \<longrightarrow> i_1 \<le> (2000 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 i_2 \<longrightarrow> addr_le a a_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_length_of_str_is t t_2 a i \<longrightarrow> p_length_of_str_is t t_2 a i_1 \<longrightarrow> is_sint32 x_3 \<longrightarrow> valid_rw t a_3 x_5 \<longrightarrow> separated (shift a (0 :: int)) x_5 a_3 x_5 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> is_sint8 a_5 \<longrightarrow> addr_le a_1 (shift a x_4) \<longrightarrow> addr_le a_6 (shift a_2 x_4) \<longrightarrow> (\<not>a_1 = a \<longrightarrow> \<not>i_2 = (0 :: int)) \<longrightarrow> (\<not>x_1 = x_2 \<longrightarrow> \<not>i_2 = (0 :: int)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_2 < x_1 \<longrightarrow> a_4 (shift a_2 i_3) = a_4 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_2 < x_1 \<longrightarrow> \<not>a_4 (shift a i_3) = (0 :: int)) \<longrightarrow> x_1 \<le> x_2 + l_length (a_4(a_6 := a_5)) a"
  sorry
end
