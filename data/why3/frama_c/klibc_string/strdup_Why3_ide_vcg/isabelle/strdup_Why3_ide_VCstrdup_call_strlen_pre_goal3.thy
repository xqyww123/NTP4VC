theory strdup_Why3_ide_VCstrdup_call_strlen_pre_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "p_length_of_str_is t t_1 a i"
  assumes fact4: "p_length_of_str_is t t_1 a i_1"
  shows "\<exists>(i_2 :: int). p_length_of_str_is t t_1 a i_2"
  sorry
end
