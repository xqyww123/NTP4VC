theory strncat_Why3_ide_VCstrncat_call_strchr_pre_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal17:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "i_1 < i"
  assumes fact3: "(0 :: int) \<le> i_2"
  assumes fact4: "i_2 < i"
  assumes fact5: "region (base a) \<le> (0 :: int)"
  assumes fact6: "region (base a_1) \<le> (0 :: int)"
  assumes fact7: "linked t"
  assumes fact8: "sconst t_1"
  assumes fact9: "is_uint32 i"
  assumes fact10: "p_length_of_str_is t t_1 a_1 i_1"
  assumes fact11: "p_length_of_str_is t t_1 a_1 i_2"
  shows "\<exists>(i_3 :: int). p_length_of_str_is t t_1 a_1 i_3"
  sorry
end
