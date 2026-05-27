theory strncmp_Why3_ide_VCstrncmp_loop_inv_3_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_uint64 i"
  assumes fact5: "p_valid_strn t t_1 a i"
  assumes fact6: "p_valid_strn t t_1 a_1 i"
  assumes fact7: "\<forall>(i_1 :: int). let x :: int = t_1 (shift a_1 i_1); x_1 :: int = t_1 (shift a i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < l_strnlen t_1 a_1 i \<longrightarrow> to_uint8 x = to_uint8 x_1 \<longleftrightarrow> x = x_1"
  shows "addr_le a a"
  and "addr_le a (shift a (l_strnlen t_1 a i))"
  sorry
end
