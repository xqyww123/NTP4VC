theory strrchr_Why3_ide_VCstrrchr_loop_assign_part2_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal12:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)) in \<not>x = (0 :: int) \<longrightarrow> x = to_sint8 i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> \<not>x_1 = x \<or> \<not>addr_lt (Mk_addr (0 :: int) (0 :: int)) a \<or> \<not>addr_le a_1 (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> \<not>(\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> \<not>x = t_1 a_2)"
  sorry
end
