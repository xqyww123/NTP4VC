theory strchr_Why3_ide_VCstrchr_exists_post_3_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal10:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = t_1 (shift a_1 i_2); x_2 :: int = t_1 a; x_3 :: int = l_length t_1 a_1; x_4 :: int = offset a_1; x_5 :: int = offset a in x = base a \<longrightarrow> x_1 = to_sint8 i_3 \<longrightarrow> x_1 = x_2 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_3 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a (shift a_1 x_3) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_4 < x_5 \<longrightarrow> \<not>t_1 (shift a_1 i_4) = x_2) \<longrightarrow> p_exists_first_occurence_of_char t t_1 a_1 i_3 (x_5 - x_4)"
  sorry
end
