theory strtok_r_Why3_ide_VCstrtok_r_loop_inv_4_preserved_part1_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal10:
  fixes t_7 :: "addr \<Rightarrow> addr"
  fixes a_4 :: "addr"
  fixes t_8 :: "addr \<Rightarrow> addr"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_6 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_2 :: "int \<Rightarrow> int"
  shows "let a_7 :: addr = t_7 a_4; a_8 :: addr = t_8 a_4; x :: int = t_5 a_8; x_1 :: int = t_5 (shift a_8 (-(1 :: int))); a_9 :: addr = shift a_1 (0 :: int); x_2 :: int = (1 :: int) + l_length t_3 a_1; a_10 :: addr = shift a_5 (0 :: int); x_3 :: int = (1 :: int) + l_length t_3 a_5; a_11 :: addr = shift a_6 (0 :: int); x_4 :: int = (1 :: int) + l_length t_4 a_6; a_12 :: addr = shift a_7 (0 :: int); x_5 :: int = l_length t_4 a_7; x_6 :: int = (1 :: int) + x_5; x_7 :: int = base a_7; a_13 :: addr = shift a_1 (l_length t_4 a_1) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_7 = a_4 \<longrightarrow> \<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_5 a_2 = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> framed t_6 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t_1 a_4 (1 :: int) \<longrightarrow> is_sint8 x \<longrightarrow> valid_rw t (t_6 a_3) (1 :: int) \<longrightarrow> valid_rw t_1 a_7 (1 :: int) \<longrightarrow> p_length_of_str_is t t_3 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_3 a_5 i_2 \<longrightarrow> p_length_of_str_is t t_3 a_5 i_3 \<longrightarrow> p_length_of_str_is t_1 t_4 a_6 i_4 \<longrightarrow> p_length_of_str_is t_1 t_4 a_7 i \<longrightarrow> is_sint8 x_1 \<longrightarrow> separated a_3 (1 :: int) a_9 x_2 \<longrightarrow> separated a_3 (1 :: int) a_10 x_3 \<longrightarrow> separated a_4 (1 :: int) a_11 x_4 \<longrightarrow> separated a_9 x_2 a_10 x_3 \<longrightarrow> separated a_7 (1 :: int) a_11 x_4 \<longrightarrow> separated a_4 (1 :: int) a_12 x_6 \<longrightarrow> separated a_12 x_6 a_11 x_4 \<longrightarrow> separated a_7 (1 :: int) a_12 x_6 \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> x_7 = base a) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> addr_le a_1 a \<and> addr_le a a_13) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> addr_le a_1 a_7 \<and> addr_le a_7 a_13) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_5 \<longrightarrow> \<not>p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> a_7 = a_2) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<and> i_5 < x_5 \<and> p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> a_7 = a_2) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_5 \<longrightarrow> \<not>p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> a_8 = Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<and> i_5 < x_5 \<and> p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> base a_8 = x_7) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<and> i_5 < x_5 \<and> p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> x_1 = (0 :: int)) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<and> i_5 < x_5 \<and> p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> p_char_in_str t_5 a_6 x) \<longrightarrow> (valid_rw t_2 a_7 (1 :: int) \<longrightarrow> (\<exists>(i_5 :: int). p_length_of_str_is t_1 t_4 a_6 i_5) \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<and> i_5 < x_5 \<and> p_char_in_str t_4 a_6 (t_4 (shift a_7 i_5))) \<longrightarrow> addr_lt a_7 a_8 \<and> addr_lt a_8 (shift a_7 (l_length t_5 a_7))) \<longrightarrow> addr_le a_1 a_2"
  sorry
end
