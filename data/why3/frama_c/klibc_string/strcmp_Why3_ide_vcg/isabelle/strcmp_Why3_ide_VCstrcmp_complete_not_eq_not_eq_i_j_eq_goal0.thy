theory strcmp_Why3_ide_VCstrcmp_complete_not_eq_not_eq_i_j_eq_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "p_length_of_str_is t t_1 a i"
  assumes fact5: "p_length_of_str_is t t_1 a i_3"
  assumes fact6: "p_length_of_str_is t t_1 a_1 i_1"
  assumes fact7: "p_length_of_str_is t t_1 a_1 i_2"
  assumes fact8: "separated (shift a_1 (0 :: int)) ((1 :: int) + l_length t_1 a_1) (shift a (0 :: int)) ((1 :: int) + l_length t_1 a)"
  shows "(\<exists>(i_5 :: int) (i_4 :: int). \<not>i_5 = i_4 \<and> p_length_of_str_is t t_1 a i_4 \<and> p_length_of_str_is t t_1 a_1 i_5) \<or> (\<exists>(i_4 :: int). p_length_of_str_is t t_1 a i_4 \<and> p_length_of_str_is t t_1 a_1 i_4 \<and> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 \<le> i_4 \<longrightarrow> t_1 (shift a_1 i_5) = t_1 (shift a i_5))) \<or> (\<exists>(i_4 :: int). p_length_of_str_is t t_1 a i_4 \<and> p_length_of_str_is t t_1 a_1 i_4 \<and> (\<exists>(i_5 :: int). \<not>t_1 (shift a_1 i_5) = t_1 (shift a i_5) \<and> (0 :: int) \<le> i_5 \<and> i_5 \<le> i_4))"
  sorry
end
