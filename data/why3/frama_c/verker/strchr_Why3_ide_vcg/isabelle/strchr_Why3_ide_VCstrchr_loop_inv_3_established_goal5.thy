theory strchr_Why3_ide_VCstrchr_loop_inv_3_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal5:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "is_sint32 i"
  assumes fact4: "addr_lt a_1 a"
  assumes fact5: "addr_le a a_1"
  assumes fact6: "p_valid_str t t_1 a"
  shows "\<not>t_1 a_1 = to_sint8 i"
  sorry
end
