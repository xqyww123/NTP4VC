theory strpbrk_Why3_ide_VCstrpbrk_not_exists_post_part1_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal10:
  fixes a :: "addr"
  fixes i_6 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  shows "let a_2 :: addr = shift a i_6; x :: int = t_1 a_2; x_1 :: int = l_length t_1 a in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> i_6 \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i_6 \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_4 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_5 \<longrightarrow> is_sint8 x \<longrightarrow> p_char_in_str t_1 a_1 x \<longrightarrow> separated (shift a (0 :: int)) ((1 :: int) + x_1) (shift a_1 (0 :: int)) ((1 :: int) + l_length t_1 a_1) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < i_6 \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a i_7))) \<longrightarrow> (\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < x_1 \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a i_7))) \<longrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int)"
  sorry
end
