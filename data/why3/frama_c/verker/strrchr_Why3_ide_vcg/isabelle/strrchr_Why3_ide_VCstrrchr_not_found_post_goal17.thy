theory strrchr_Why3_ide_VCstrrchr_not_found_post_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal17:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a_1; a_2 :: addr = shift a_1 x; x_1 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)) in t_1 a = (0 :: int) \<longrightarrow> to_sint8 i = (0 :: int) \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> shift a_1 ((1 :: int) + x) = shift a (1 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> ((\<exists>(a_3 :: addr). t_1 a_3 = (0 :: int) \<and> addr_le a_1 a_3 \<and> addr_lt a_3 a_2) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> \<not>x_1 = (0 :: int) \<or> \<not>addr_lt (Mk_addr (0 :: int) (0 :: int)) a \<or> \<not>addr_le a_1 (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>t_1 a_3 = (0 :: int)) \<longrightarrow> (\<forall>(a_3 :: addr). addr_le a_1 a_3 \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> \<not>t_1 a_3 = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a"
  sorry
end
