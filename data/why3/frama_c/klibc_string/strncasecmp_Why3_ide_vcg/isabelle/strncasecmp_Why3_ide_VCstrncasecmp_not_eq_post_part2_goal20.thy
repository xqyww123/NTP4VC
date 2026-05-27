theory strncasecmp_Why3_ide_VCstrncasecmp_not_eq_post_part2_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper"
begin
theorem goal20:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_7 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_6 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  shows "let x :: int = i_1 - i_2; a_8 :: addr = shift a_1 x; a_9 :: addr = shift a x; x_1 :: int = t_1 a_9; a_10 :: addr = shift a_6 (0 :: int); a_11 :: addr = shift a_7 (0 :: int) in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>l_toupper (to_uint8 (t_2 (shift a_7 i_7))) = l_toupper (to_uint8 (t_2 (shift a_6 i_7))) \<longrightarrow> t_1 a_8 = (0 :: int) \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_1 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> x_1 \<le> (255 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> p_length_of_str_is t t_2 a_6 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_6 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_4 \<longrightarrow> p_length_of_str_is t t_2 a_7 i_5 \<longrightarrow> valid_rw t a_10 i_1 \<longrightarrow> valid_rw t a_11 i_1 \<longrightarrow> separated a_11 i_1 a_10 i_1 \<longrightarrow> addr_le a_2 a_9 \<longrightarrow> addr_le a_4 a_8 \<longrightarrow> addr_le a_9 (shift a_3 i_1) \<longrightarrow> addr_le a_8 (shift a_5 i_1) \<longrightarrow> is_uint8 x_1 \<longrightarrow> (p_is_lower (0 :: int) \<longrightarrow> i = -(32 :: int)) \<longrightarrow> (p_is_upper (0 :: int) \<longrightarrow> i = (0 :: int)) \<longrightarrow> (\<not>p_is_lower (0 :: int) \<longrightarrow> \<not>p_is_upper (0 :: int) \<longrightarrow> i = (0 :: int)) \<longrightarrow> (p_is_upper x_1 \<longrightarrow> x_1 = i) \<longrightarrow> (p_is_lower x_1 \<longrightarrow> x_1 = (32 :: int) + i) \<longrightarrow> (\<not>p_is_lower x_1 \<longrightarrow> \<not>p_is_upper x_1 \<longrightarrow> x_1 = i) \<longrightarrow> \<not>(\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 + i_2 < i_1 \<longrightarrow> l_toupper (to_uint8 (t_2 (shift a_7 i_8))) = l_toupper (to_uint8 (t_2 (shift a_6 i_8))))"
  sorry
end
