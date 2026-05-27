theory strcat_Why3_ide_VCstrcat_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_7 :: "int"
  fixes i_6 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  shows "let x :: int = base a_2; a_3 :: addr = shift a (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_3 a_3 ((1 :: int) + l_length t_2 a_1); x_1 :: int = l_length a_4 a_1; x_2 :: int = t_3 a; x_3 :: int = l_length t_3 a_1; x_4 :: int = (1 :: int) + x_3; a_5 :: addr = shift a_2 (0 :: int); x_5 :: int = l_length t_3 a_2; a_6 :: addr = shift a_1 (0 :: int) in \<not>a_1 = a \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i_7 \<le> x_1 \<longrightarrow> i_6 \<le> (2000 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_sint8 x_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> p_length_of_str_is t t_3 a_1 i \<longrightarrow> p_length_of_str_is t t_3 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_3 a_1 i_6 \<longrightarrow> p_length_of_str_is t t_3 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_3 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_3 a_2 i_4 \<longrightarrow> valid_rw t a_3 x_4 \<longrightarrow> valid_rw t a_5 (x_3 + x_5) \<longrightarrow> separated a_6 x_4 a_3 x_4 \<longrightarrow> separated a_5 ((1 :: int) + x_5) a_6 x_4 \<longrightarrow> p_length_of_str_is t a_4 a i_5 \<longrightarrow> p_length_of_str_is t a_4 a_1 i_5 \<longrightarrow> ((\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 < x_5 \<longrightarrow> \<not>t_3 (shift a_2 i_8) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_8 :: int). t_3 (shift a_2 i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < x_5) \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> ((\<exists>(i_8 :: int). t_3 (shift a_2 i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < x_5) \<longrightarrow> x = base a) \<longrightarrow> ((\<exists>(i_8 :: int). t_3 (shift a_2 i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < x_5) \<longrightarrow> p_exists_first_occurence_of_char t t_3 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_8 :: int). t_3 (shift a_2 i_8) = (0 :: int) \<and> (0 :: int) \<le> i_8 \<and> i_8 < x_5) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_5)) \<longrightarrow> (\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 \<le> x_1 \<longrightarrow> a_4 (shift a_1 i_8) = a_4 (shift a i_8)) \<longrightarrow> a_4 (shift a_2 (i_7 + x_5)) = a_4 (shift a_1 i_7)"
  sorry
end
