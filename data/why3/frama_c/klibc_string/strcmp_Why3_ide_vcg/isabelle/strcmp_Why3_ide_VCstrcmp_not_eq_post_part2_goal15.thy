theory strcmp_Why3_ide_VCstrcmp_not_eq_post_part2_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal15:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = base a; x_1 :: int = offset a_1; x_2 :: int = offset a; a_3 :: addr = shift a_2 (x_1 - x_2); x_3 :: int = l_length t_1 a; x_4 :: int = l_length t_1 a_2 in t_1 a_1 = (0 :: int) \<longrightarrow> base a_1 = x \<longrightarrow> \<not>t_1 (shift a_2 i_4) = t_1 (shift a i_4) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> i_5 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a i_5 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_5 \<longrightarrow> addr_le a_1 (shift a x_3) \<longrightarrow> separated (shift a_2 (0 :: int)) ((1 :: int) + x_4) (shift a (0 :: int)) ((1 :: int) + x_3) \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_3 (shift a_2 x_4) \<longrightarrow> \<not>(\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 + x_2 < x_1 \<longrightarrow> t_1 (shift a_2 i_6) = t_1 (shift a i_6))"
  sorry
end
