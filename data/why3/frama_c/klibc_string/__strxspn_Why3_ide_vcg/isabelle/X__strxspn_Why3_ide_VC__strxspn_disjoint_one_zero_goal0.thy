theory X__strxspn_Why3_ide_VC__strxspn_disjoint_one_zero_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_sint32 (0 :: int)"
  assumes fact5: "is_sint8 (t_1 a_1)"
  assumes fact6: "p_length_of_str_is t t_1 a i_1"
  assumes fact7: "p_length_of_str_is t t_1 a i_3"
  assumes fact8: "p_length_of_str_is t t_1 a_1 i_2"
  assumes fact9: "p_length_of_str_is t t_1 a_1 i_4"
  assumes fact10: "separated (shift a (0 :: int)) ((1 :: int) + l_length t_1 a) (shift a_1 (0 :: int)) ((1 :: int) + l_length t_1 a_1)"
  assumes fact11: "True \<or> (0 :: int) = (1 :: int)"
  shows "\<not>True \<or> \<not>(0 :: int) = (1 :: int)"
  sorry
end
