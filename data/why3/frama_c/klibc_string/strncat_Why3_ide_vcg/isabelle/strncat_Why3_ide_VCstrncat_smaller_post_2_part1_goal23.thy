theory strncat_Why3_ide_VCstrncat_smaller_post_2_part1_goal23
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal23:
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
  fixes i_4 :: "int"
  fixes i_6 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_5 :: "int"
  shows "let x_1 :: int = i_1 - i; a_3 :: addr = shift a_1 x_1; x_2 :: int = l_length t_3 a_2; x_3 :: int = base a_2; a_4 :: addr = shift a_2 (i_1 + x_2 - i); m :: addr \<Rightarrow> int = t_3(a_4 := 0 :: int); x_4 :: int = l_length m a_2; x_5 :: int = t_2 a; a_5 :: addr = shift a_2 (0 :: int); x_6 :: int = (2 :: int) * i_1; x_7 :: int = i_1 + x_2; x_8 :: int = l_length t_2 a_2 in \<not>i = (0 :: int) \<longrightarrow> t_3 a_3 = (0 :: int) \<longrightarrow> havoc t_1 t_2 (shift a_2 x_2) x_1 = t_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> i_1 < l_length t_2 a_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x_3 \<le> (0 :: int) \<longrightarrow> x_4 \<le> i_6 \<longrightarrow> i_6 < i_1 + x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_4 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_5 \<longrightarrow> valid_rw t a_5 x_6 \<longrightarrow> separated (shift a_1 (0 :: int)) x_6 a_5 i_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_3 (shift a_1 i_1) \<longrightarrow> addr_le (shift a_2 i_1) a_4 \<longrightarrow> addr_le a_4 (shift a_2 x_7) \<longrightarrow> ((\<forall>(i_7 :: int). (0 :: int) \<le> i_7 \<longrightarrow> i_7 < x_8 \<longrightarrow> \<not>t_2 (shift a_2 i_7) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_7 :: int). t_2 (shift a_2 i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < x_8) \<longrightarrow> x_5 = (0 :: int)) \<longrightarrow> ((\<exists>(i_7 :: int). t_2 (shift a_2 i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < x_8) \<longrightarrow> x_3 = base a) \<longrightarrow> ((\<exists>(i_7 :: int). t_2 (shift a_2 i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < x_8) \<longrightarrow> p_exists_first_occurence_of_char t t_2 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_7 :: int). t_2 (shift a_2 i_7) = (0 :: int) \<and> (0 :: int) \<le> i_7 \<and> i_7 < x_8) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_8)) \<longrightarrow> (\<forall>(i_7 :: int). x_2 \<le> i_7 \<longrightarrow> i_7 + i < x_7 \<longrightarrow> t_3 (shift a_2 (i_7 + x_2)) = t_3 (shift a_1 i_7)) \<longrightarrow> m (shift a_2 (i_1 + i_6)) = m (shift a_1 i_6)"
  sorry
end
