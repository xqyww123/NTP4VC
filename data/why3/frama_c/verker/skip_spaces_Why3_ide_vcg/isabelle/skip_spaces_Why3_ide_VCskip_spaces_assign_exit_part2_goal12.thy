theory skip_spaces_Why3_ide_VCskip_spaces_assign_exit_part2_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal12:
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "addr_le a_1 a"
  assumes fact4: "is_sint8 (t_1 a)"
  assumes fact5: "p_valid_str t t_1 a"
  assumes fact6: "p_valid_str t t_1 a_1"
  assumes fact7: "addr_le a (shift a_1 (l_strlen t_1 a_1))"
  shows "\<not>(\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> p_isspace (t_1 a_2))"
  sorry
end
