theory strstr_Why3_ide_VCstrstr_call_strlen_pre_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_sint32 (l_length t_1 a)"
  assumes fact5: "p_length_of_str_is t t_1 a i"
  shows "\<exists>(i_1 :: int). p_length_of_str_is t t_1 a_1 i_1"
  sorry
end
