theory strcasecmp_Why3_ide_VCstrcasecmp_eq_post_part1_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal18:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = base a; x_1 :: int = t_1 a_1; x_2 :: int = offset a_1; x_3 :: int = offset a; a_3 :: addr = shift a_2 (x_2 - x_3); x_4 :: int = t_1 a_3; x_5 :: int = i + i_1; x_6 :: int = l_length t_1 a; x_7 :: int = l_length t_1 a_2; x_8 :: int = to_uint8 x_1; x_9 :: int = to_uint8 x_4 in \<not>i_1 = (0 :: int) \<longrightarrow> base a_1 = x \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_4 \<longrightarrow> x_1 \<le> (255 :: int) \<longrightarrow> x_4 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint32 x_5 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_5 \<longrightarrow> p_length_of_str_is t t_1 a i_6 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_4 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_6 \<longrightarrow> addr_le a_1 (shift a x_6) \<longrightarrow> separated (shift a_2 (0 :: int)) ((1 :: int) + x_7) (shift a (0 :: int)) ((1 :: int) + x_6) \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_3 (shift a_2 x_7) \<longrightarrow> is_sint8 x_4 \<longrightarrow> (p_is_upper x_8 \<longrightarrow> x_1 = i) \<longrightarrow> (p_is_lower x_8 \<longrightarrow> x_1 = (32 :: int) + i) \<longrightarrow> (\<not>p_is_lower x_8 \<longrightarrow> \<not>p_is_upper x_8 \<longrightarrow> x_1 = i) \<longrightarrow> (p_is_upper x_9 \<longrightarrow> x_4 = x_5) \<longrightarrow> (p_is_lower x_9 \<longrightarrow> x_4 = (32 :: int) + i + i_1) \<longrightarrow> (\<not>p_is_lower x_9 \<longrightarrow> \<not>p_is_upper x_9 \<longrightarrow> x_4 = x_5) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 + x_3 < x_2 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_2 i_7))) = l_toupper (to_uint8 (t_1 (shift a i_7)))) \<longrightarrow> \<not>(\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 \<le> i_6 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_2 i_7))) = l_toupper (to_uint8 (t_1 (shift a i_7))))"
  sorry
end
