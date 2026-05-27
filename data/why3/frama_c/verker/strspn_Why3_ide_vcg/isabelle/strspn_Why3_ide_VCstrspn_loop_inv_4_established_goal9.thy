theory strspn_Why3_ide_VCstrspn_loop_inv_4_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "addr_lt a_2 a"
  assumes fact5: "addr_le a a_2"
  assumes fact6: "p_valid_str t t_1 a"
  assumes fact7: "p_valid_str t t_1 a_1"
  shows "\<exists>(a_3 :: addr). t_1 a_2 = t_1 a_3 \<and> addr_le a_1 a_3 \<and> addr_lt a_3 (shift a_1 (l_strlen t_1 a_1))"
  sorry
end
