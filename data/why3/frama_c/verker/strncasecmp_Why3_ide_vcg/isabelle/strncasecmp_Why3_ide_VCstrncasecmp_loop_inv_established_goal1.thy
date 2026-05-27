theory strncasecmp_Why3_ide_VCstrncasecmp_loop_inv_established_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal1:
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "\<not>i = (0 :: int)"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_1"
  assumes fact5: "is_uint64 i"
  assumes fact6: "p_valid_strn t t_1 a i"
  assumes fact7: "p_valid_strn t t_1 a_1 i"
  shows "(0 :: int) \<le> i"
  sorry
end
