theory strlcat_Why3_ide_VCstrlcat_loop_inv_8_preserved_part2_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal15:
  fixes a_1 :: "addr"
  fixes i_8 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_7 :: "int"
  fixes i_9 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_8; a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i_1; a_5 :: addr = shift a i_6; a_6 :: int = a_4 a_5; x :: int = l_length a_4 a; x_1 :: int = (1 :: int) + i_2 + i_3; x_2 :: int = (1 :: int) + i_4 + i_5; a_7 :: addr = shift a (0 :: int) in t_2 a_2 = (0 :: int) \<longrightarrow> \<not>a_6 = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_8 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> i_1 \<le> i_6 \<longrightarrow> i_7 \<le> i_6 \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> i_8 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> to_uint32 ((1 :: int) + i_9) \<longrightarrow> i_6 \<le> x \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_8 \<longrightarrow> is_uint32 i_9 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_6 \<longrightarrow> is_sint32 ((1 :: int) + i_6) \<longrightarrow> p_length_of_str_is t t_2 a i_3 \<longrightarrow> p_length_of_str_is t t_2 a i_5 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_4 \<longrightarrow> addr_le a a_5 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> valid_rw t a_3 x_1 \<longrightarrow> valid_rw t a_3 x_2 \<longrightarrow> separated a_7 ((1 :: int) + i_3) a_3 x_1 \<longrightarrow> separated a_7 ((1 :: int) + i_5) a_3 x_2 \<longrightarrow> addr_le a_2 (shift a_1 (l_length t_2 a_1)) \<longrightarrow> is_sint8 a_6 \<longrightarrow> addr_le a_5 (shift a x) \<longrightarrow> (\<forall>(i_10 :: int). (0 :: int) \<le> i_10 \<longrightarrow> i_10 < i_8 \<longrightarrow> \<not>t_2 (shift a_1 i_10) = (0 :: int)) \<longrightarrow> (\<forall>(i_10 :: int). (0 :: int) \<le> i_10 \<longrightarrow> i_10 < i_6 \<longrightarrow> \<not>a_4 (shift a i_10) = (0 :: int)) \<longrightarrow> \<not>a_4 (shift a i_7) = (0 :: int)"
  sorry
end
