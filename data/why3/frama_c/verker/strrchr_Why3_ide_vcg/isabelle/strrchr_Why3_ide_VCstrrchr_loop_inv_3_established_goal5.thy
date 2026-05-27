theory strrchr_Why3_ide_VCstrrchr_loop_inv_3_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
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
  assumes fact4: "is_sint8 (t_1 (Mk_addr (0 :: int) (0 :: int)))"
  assumes fact5: "p_valid_str t t_1 a"
  shows "\<not>t_1 a_1 = to_sint8 i \<or> \<not>addr_lt a_1 a \<or> \<not>addr_le a a_1"
  sorry
end
