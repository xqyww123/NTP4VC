theory strncasecmp_Why3_ide_VCstrncasecmp_eq_post_part1_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper"
begin
theorem goal19:
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_7 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  shows "let x :: int = i_2 - i_3; a_8 :: addr = shift a x; x_1 :: int = t_1 a_8; a_9 :: addr = shift a_1 x; x_2 :: int = t_1 a_9; x_3 :: int = i + i_1; a_10 :: addr = shift a_6 (0 :: int); a_11 :: addr = shift a_7 (0 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> x_1 \<le> (255 :: int) \<longrightarrow> x_2 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_4 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_7 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_5 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_6 \<longrightarrow> valid_rw t a_10 i_2 \<longrightarrow> valid_rw t a_11 i_2 \<longrightarrow> separated a_11 i_2 a_10 i_2 \<longrightarrow> addr_le a_2 a_8 \<longrightarrow> addr_le a_4 a_9 \<longrightarrow> addr_le a_8 (shift a_3 i_2) \<longrightarrow> addr_le a_9 (shift a_5 i_2) \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x_2 \<longrightarrow> (p_is_upper x_1 \<longrightarrow> x_1 = i) \<longrightarrow> (p_is_lower x_1 \<longrightarrow> x_1 = (32 :: int) + i) \<longrightarrow> (p_is_upper x_2 \<longrightarrow> x_2 = x_3) \<longrightarrow> (p_is_lower x_2 \<longrightarrow> x_2 = (32 :: int) + i + i_1) \<longrightarrow> (\<not>p_is_lower x_1 \<longrightarrow> \<not>p_is_upper x_1 \<longrightarrow> x_1 = i) \<longrightarrow> (\<not>p_is_lower x_2 \<longrightarrow> \<not>p_is_upper x_2 \<longrightarrow> x_2 = x_3) \<longrightarrow> (\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 < i_2 \<longrightarrow> l_toupper (to_uint8 (t_2 (shift a_7 i_8))) = l_toupper (to_uint8 (t_2 (shift a_6 i_8)))) \<longrightarrow> \<not>(\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 + i_3 < i_2 \<longrightarrow> l_toupper (to_uint8 (t_2 (shift a_7 i_8))) = l_toupper (to_uint8 (t_2 (shift a_6 i_8))))"
  sorry
end
