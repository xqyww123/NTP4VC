theory strcat_Why3_ide_VCstrcat_call_strcpy_pre_3_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal6:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = base a; x_1 :: int = base a_1; x_2 :: int = t_1 a; a_2 :: addr = shift a_1 (0 :: int); x_3 :: int = l_length t_1 a; x_4 :: int = l_length t_1 a_1 in region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a i_3 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_1 i_4 \<longrightarrow> valid_rw t a_2 (x_3 + x_4) \<longrightarrow> separated a_2 ((1 :: int) + x_4) (shift a (0 :: int)) ((1 :: int) + x_3) \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_4 \<longrightarrow> \<not>t_1 (shift a_1 i_5) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_1 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_4) \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_1 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_4) \<longrightarrow> x_1 = x) \<longrightarrow> ((\<exists>(i_5 :: int). t_1 (shift a_1 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_4) \<longrightarrow> p_exists_first_occurence_of_char t t_1 a_1 (0 :: int) (offset a - offset a_1)) \<longrightarrow> \<not>((\<exists>(i_5 :: int). t_1 (shift a_1 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_4) \<longrightarrow> addr_le a_1 a \<and> addr_le a (shift a_1 x_4))"
  sorry
end
