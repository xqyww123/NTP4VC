theory strpbrk_Why3_ide_VCstrpbrk_exists_post_part2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_8 :: "int"
  fixes i_4 :: "int"
  fixes i_7 :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_6 :: "int"
  shows "let x :: int = l_length t_1 a in t_1 (shift a i_8) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> (0 :: int) \<le> i_8 \<longrightarrow> i_4 < x \<longrightarrow> i_8 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_7 + offset a < (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i_8 \<longrightarrow> is_sint8 (t_1 (Mk_addr (0 :: int) (0 :: int))) \<longrightarrow> p_char_in_str t_1 a_1 (0 :: int) \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_2 \<longrightarrow> p_length_of_str_is t t_1 a i_5 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_6 \<longrightarrow> p_char_in_str t_1 a_1 (t_1 (shift a i_4)) \<longrightarrow> separated (shift a (0 :: int)) ((1 :: int) + x) (shift a_1 (0 :: int)) ((1 :: int) + l_length t_1 a_1) \<longrightarrow> (\<forall>(i_9 :: int). (0 :: int) \<le> i_9 \<longrightarrow> i_9 < i_8 \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a i_9))) \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a i_7))"
  sorry
end
