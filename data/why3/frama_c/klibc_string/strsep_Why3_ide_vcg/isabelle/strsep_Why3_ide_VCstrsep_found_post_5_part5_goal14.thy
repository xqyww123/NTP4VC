theory strsep_Why3_ide_VCstrsep_found_post_5_part5_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1" "Why3STD.Cint_Cint"
begin
theorem goal14:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_7 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_6 :: "int"
  shows "let a_2 :: addr = t_2 a; x :: int = l_length t_1 a_2; x_1 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)); a_3 :: addr = shift a_1 (0 :: int); x_2 :: int = (1 :: int) + l_length t_1 a_1; a_4 :: addr = shift a_2 (0 :: int); x_3 :: int = (1 :: int) + x in \<not>a_2 = a \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_5 < x \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_7 \<longrightarrow> is_sint8 (t_1 (shift (Mk_addr (0 :: int) (0 :: int)) (-(1 :: int)))) \<longrightarrow> p_length_of_str_is t t_1 a_2 i \<longrightarrow> p_length_of_str_is t t_1 a_2 i_4 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_6 \<longrightarrow> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_5)) \<longrightarrow> separated a (1 :: int) a_3 x_2 \<longrightarrow> separated a_2 (1 :: int) a_3 x_2 \<longrightarrow> separated a (1 :: int) a_4 x_3 \<longrightarrow> separated a_4 x_3 a_3 x_2 \<longrightarrow> separated a_2 (1 :: int) a_4 x_3 \<longrightarrow> ((\<exists>(i_8 :: int). (0 :: int) \<le> i_8 \<and> i_8 < x \<and> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_8))) \<longrightarrow> base a_2 = (0 :: int)) \<longrightarrow> ((\<exists>(i_8 :: int). (0 :: int) \<le> i_8 \<and> i_8 < x \<and> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_8))) \<longrightarrow> p_char_in_str t_1 a_1 x_1) \<longrightarrow> ((\<exists>(i_8 :: int). (0 :: int) \<le> i_8 \<and> i_8 < x \<and> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_8))) \<longrightarrow> addr_le a_2 (Mk_addr (0 :: int) (0 :: int)) \<and> addr_lt (Mk_addr (0 :: int) (0 :: int)) (shift a_2 x)) \<longrightarrow> ((\<exists>(i_8 :: int). (0 :: int) \<le> i_8 \<and> i_8 < x \<and> p_char_in_str t_1 a_1 (t_1 (shift a_2 i_8))) \<longrightarrow> (\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 + offset a_2 < (0 :: int) \<longrightarrow> \<not>p_char_in_str t_1 a_1 (t_1 (shift a_2 i_8)))) \<longrightarrow> addr_lt a_2 (Mk_addr (0 :: int) (0 :: int))"
  sorry
end
