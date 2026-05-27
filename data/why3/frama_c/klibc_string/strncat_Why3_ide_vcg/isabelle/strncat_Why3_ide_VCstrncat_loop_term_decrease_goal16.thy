theory strncat_Why3_ide_VCstrncat_loop_term_decrease_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal16:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  shows "let x_1 :: int = i_1 - i; a_3 :: addr = shift a_1 x_1; x_2 :: int = t_3 a_3; x_3 :: int = l_length t_3 a_2; x_4 :: int = base a_2; x_5 :: int = t_2 a; a_4 :: addr = shift a_2 (i_1 + x_3 - i); x_6 :: int = i_1 + x_3; x_7 :: int = l_length t_2 a_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> havoc t_1 t_2 (shift a_2 x_3) x_1 = t_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x_4 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_4 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_3 (shift a_1 i_1) \<longrightarrow> is_sint8 x_2 \<longrightarrow> addr_le (shift a_2 i_1) a_4 \<longrightarrow> addr_le a_4 (shift a_2 x_6) \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_7 \<longrightarrow> \<not>t_2 (shift a_2 i_5) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_7) \<longrightarrow> x_5 = (0 :: int)) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_7) \<longrightarrow> x_4 = base a) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_7) \<longrightarrow> p_exists_first_occurence_of_char t t_2 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_7) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_7)) \<longrightarrow> (\<forall>(i_5 :: int). x_3 \<le> i_5 \<longrightarrow> i_5 + i < x_6 \<longrightarrow> t_3 (shift a_2 (i_5 + x_3)) = t_3 (shift a_1 i_5)) \<longrightarrow> to_uint32 (i - (1 :: int)) < i"
  sorry
end
