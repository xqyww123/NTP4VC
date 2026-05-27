theory strncat_Why3_ide_VCstrncat_larger_assign_normal_part15_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal22:
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  shows "let x :: int = l_length t_3 a_2; x_1 :: int = l_length t_2 a_1; x_2 :: int = base a_2; x_3 :: int = t_2 a; a_3 :: addr = shift a_1 i; a_4 :: addr = shift a_2 (0 :: int); x_4 :: int = i + x_1; a_5 :: addr = shift a_2 i; x_5 :: int = i + x; a_6 :: addr = shift a_2 x_5; x_6 :: int = l_length t_2 a_2 in havoc t_1 t_2 (shift a_2 x) i = t_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> x_1 \<le> i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_sint8 x_3 \<longrightarrow> p_length_of_str_is t t_2 a_1 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_2 a_2 i_4 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_3 a_3 \<longrightarrow> valid_rw t a_4 x_4 \<longrightarrow> separated (shift a_1 (0 :: int)) x_4 a_4 i \<longrightarrow> addr_le a_5 a_6 \<longrightarrow> addr_le a_6 a_6 \<longrightarrow> \<not>invalid t a_6 (1 :: int) \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < x_6 \<longrightarrow> \<not>t_2 (shift a_2 i_5) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_6) \<longrightarrow> x_3 = (0 :: int)) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_6) \<longrightarrow> x_2 = base a) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_6) \<longrightarrow> p_exists_first_occurence_of_char t t_2 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_5 :: int). t_2 (shift a_2 i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 < x_6) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_6)) \<longrightarrow> (\<forall>(i_5 :: int). x \<le> i_5 \<longrightarrow> i_5 < x_5 \<longrightarrow> t_3 (shift a_2 (i_5 + x)) = t_3 (shift a_1 i_5)) \<longrightarrow> included a_6 (1 :: int) a_5 (x_1 + x_6 - i)"
  sorry
end
