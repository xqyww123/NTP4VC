theory strrchr_Why3_ide_VCstrrchr_assert_3_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_2; x_1 :: int = l_strlen t_1 a_1; a_3 :: addr = shift a_1 x_1; x_2 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)) in t_1 a = (0 :: int) \<longrightarrow> x = to_sint8 i \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> shift a_1 ((1 :: int) + x_1) = shift a (1 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_lt a_2 a_3 \<longrightarrow> addr_le a a_3 \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a \<or> \<not>x = (0 :: int) \<longrightarrow> \<not>x_2 = x \<or> \<not>addr_lt (Mk_addr (0 :: int) (0 :: int)) a \<or> \<not>addr_le a_1 (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> \<not>(\<forall>(a_4 :: addr). addr_lt a_4 a \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> \<not>x = t_1 a_4)"
  sorry
end
