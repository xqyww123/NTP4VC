theory strcasecmp_Why3_ide_VCstrcasecmp_call_toupper_pre_part2_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.A_ToUpper_A_ToUpper" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic2_Axiomatic2"
begin
theorem goal15:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = base a; x_1 :: int = l_length t_1 a; x_2 :: int = l_length t_1 a_2; x_3 :: int = offset a_1; x_4 :: int = offset a; a_3 :: addr = shift a_2 (x_3 - x_4); x_5 :: int = t_1 a_3 in base a_1 = x \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> addr_le a_1 (shift a x_1) \<longrightarrow> separated (shift a_2 (0 :: int)) ((1 :: int) + x_2) (shift a (0 :: int)) ((1 :: int) + x_1) \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_3 (shift a_2 x_2) \<longrightarrow> is_sint8 x_5 \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_4 < x_3 \<longrightarrow> l_toupper (to_uint8 (t_1 (shift a_2 i_4))) = l_toupper (to_uint8 (t_1 (shift a i_4)))) \<longrightarrow> x_5 \<le> (255 :: int)"
  sorry
end
