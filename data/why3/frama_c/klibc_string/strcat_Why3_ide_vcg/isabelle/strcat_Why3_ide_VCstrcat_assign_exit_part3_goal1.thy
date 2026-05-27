theory strcat_Why3_ide_VCstrcat_assign_exit_part3_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_2 a; a_3 :: addr = shift a (0 :: int); x_2 :: int = l_length t_2 a_1; x_3 :: int = (1 :: int) + x_2; a_4 :: addr = shift a_2 (0 :: int); x_4 :: int = l_length t_2 a_2; x_5 :: int = (1 :: int) + l_length t_1 a_1; a_5 :: addr = shift a_1 (0 :: int); a_6 :: addr = shift a_2 x_4 in \<not>a_1 = a \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i_5 \<le> (2000 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 x_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> p_length_of_str_is t t_2 a_1 i \<longrightarrow> p_length_of_str_is t t_2 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_5 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_4 \<longrightarrow> valid_rw t a_3 x_3 \<longrightarrow> valid_rw t a_4 (x_2 + x_4) \<longrightarrow> \<not>invalid t a_3 x_5 \<longrightarrow> separated a_5 x_3 a_3 x_3 \<longrightarrow> separated a_4 ((1 :: int) + x_4) a_5 x_3 \<longrightarrow> ((\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < x_4 \<longrightarrow> \<not>t_2 (shift a_2 i_6) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_6 :: int). t_2 (shift a_2 i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < x_4) \<longrightarrow> x_1 = (0 :: int)) \<longrightarrow> ((\<exists>(i_6 :: int). t_2 (shift a_2 i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < x_4) \<longrightarrow> x = base a) \<longrightarrow> ((\<exists>(i_6 :: int). t_2 (shift a_2 i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < x_4) \<longrightarrow> p_exists_first_occurence_of_char t t_2 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_6 :: int). t_2 (shift a_2 i_6) = (0 :: int) \<and> (0 :: int) \<le> i_6 \<and> i_6 < x_4) \<longrightarrow> addr_le a_2 a \<and> addr_le a a_6) \<longrightarrow> included a_3 x_5 a_6 x_3"
  sorry
end
