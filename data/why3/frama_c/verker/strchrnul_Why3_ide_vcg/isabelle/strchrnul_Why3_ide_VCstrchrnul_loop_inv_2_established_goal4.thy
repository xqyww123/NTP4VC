theory strchrnul_Why3_ide_VCstrchrnul_loop_inv_2_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_1"
  assumes fact3: "p_valid_str t t_1 a"
  shows "addr_le a a"
  and "addr_le a (shift a (l_strlen t_1 a))"
  sorry
end
