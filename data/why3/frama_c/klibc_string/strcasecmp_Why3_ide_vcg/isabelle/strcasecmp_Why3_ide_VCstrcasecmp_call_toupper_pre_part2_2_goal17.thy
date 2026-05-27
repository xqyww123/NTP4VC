theory strcasecmp_Why3_ide_VCstrcasecmp_call_toupper_pre_part2_2_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal17:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = offset a; x_2 :: int = offset a_1; a_3 :: addr = shift a_2 (x_1 - x_2); x_3 :: int = t_1 a_3; x_4 :: int = t_1 a; x_5 :: int = l_length t_1 a_1; x_6 :: int = l_length t_1 a_2; x_7 :: int = to_uint8 x_3 in x = base a \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x_4 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_4 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_3 \<longrightarrow> addr_le a (shift a_1 x_5) \<longrightarrow> separated (shift a_2 (0 :: int)) ((1 :: int) + x_6) (shift a_1 (0 :: int)) ((1 :: int) + x_5) \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_3 (shift a_2 x_6) \<longrightarrow> is_sint8 x_3 \<longrightarrow> (p_is_upper x_7 \<longrightarrow> x_3 = i) \<longrightarrow> (p_is_lower x_7 \<longrightarrow> x_3 = (32 :: int) + i) \<longrightarrow> (\<not>p_is_lower x_7 \<longrightarrow> \<not>p_is_upper x_7 \<longrightarrow> x_3 = i) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 + x_2 < x_1 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_2 i_5))) = l_toupper (to_uint8 (t_1 (shift a_1 i_5)))) \<longrightarrow> x_4 \<le> (255 :: int)"
  sorry
end
