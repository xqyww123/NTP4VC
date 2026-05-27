theory strcasecmp_Why3_ide_VCstrcasecmp_loop_inv_2_established_part1_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal10:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "p_length_of_str_is t t_1 a i_1"
  assumes fact5: "p_length_of_str_is t t_1 a i_2"
  assumes fact6: "p_length_of_str_is t t_1 a_1 i"
  assumes fact7: "p_length_of_str_is t t_1 a_1 i_3"
  assumes fact8: "separated (shift a (0 :: int)) ((1 :: int) + l_length t_1 a) (shift a_1 (0 :: int)) ((1 :: int) + l_length t_1 a_1)"
  shows "addr_le a_1 a_1"
  sorry
end
