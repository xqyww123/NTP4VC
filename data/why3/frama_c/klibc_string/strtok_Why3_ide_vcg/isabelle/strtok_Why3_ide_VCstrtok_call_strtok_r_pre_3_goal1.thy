theory strtok_Why3_ide_VCstrtok_call_strtok_r_pre_3_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "region (base a_2) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  shows "\<exists>(i :: int). p_length_of_str_is t t_1 a_2 i"
  sorry
end
