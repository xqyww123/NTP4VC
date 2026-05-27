theory strcasecmp_Why3_ide_VCstrcasecmp_loop_inv_preserved_part2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = offset a_2; x_2 :: int = offset a_1; a_3 :: addr = shift a (x_1 - x_2); x_4 :: int = t_1 a_3; x_5 :: int = t_1 a_2; x_6 :: int = l_length t_1 a_1; x_7 :: int = l_length t_1 a; a_4 :: addr = shift a x_7; x_8 :: int = to_uint8 x_5; x_9 :: int = (32 :: int) + i; x_10 :: int = to_uint8 x_4 in base a_2 = x \<longrightarrow> \<not>x_4 = (0 :: int) \<longrightarrow> (0 :: int) \<le> x_5 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_4 \<longrightarrow> x_5 \<le> (255 :: int) \<longrightarrow> x_4 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_4 \<longrightarrow> addr_le a_2 (shift a_1 x_6) \<longrightarrow> separated (shift a (0 :: int)) ((1 :: int) + x_7) (shift a_1 (0 :: int)) ((1 :: int) + x_6) \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_3 a_4 \<longrightarrow> is_sint8 x_4 \<longrightarrow> (p_is_upper x_8 \<longrightarrow> x_5 = i) \<longrightarrow> (p_is_lower x_8 \<longrightarrow> x_5 = x_9) \<longrightarrow> (\<not>p_is_lower x_8 \<longrightarrow> \<not>p_is_upper x_8 \<longrightarrow> x_5 = i) \<longrightarrow> (p_is_upper x_10 \<longrightarrow> x_4 = i) \<longrightarrow> (p_is_lower x_10 \<longrightarrow> x_4 = x_9) \<longrightarrow> (\<not>p_is_lower x_10 \<longrightarrow> \<not>p_is_upper x_10 \<longrightarrow> x_4 = i) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 + x_2 < x_1 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_1 i_5))) = l_toupper (to_uint8 (t_1 (shift a i_5)))) \<longrightarrow> addr_le (shift a ((1 :: int) + x_1 - x_2)) a_4"
  sorry
end
