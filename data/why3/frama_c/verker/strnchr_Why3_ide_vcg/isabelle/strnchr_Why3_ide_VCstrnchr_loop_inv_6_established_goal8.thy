theory strnchr_Why3_ide_VCstrnchr_loop_inv_6_established_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "is_sint32 i_1"
  assumes fact4: "is_uint64 i"
  assumes fact5: "addr_lt a_1 a"
  assumes fact6: "addr_le a a_1"
  assumes fact7: "p_valid_strn t t_1 a i"
  shows "\<not>t_1 a_1 = to_sint8 i_1"
  sorry
end
