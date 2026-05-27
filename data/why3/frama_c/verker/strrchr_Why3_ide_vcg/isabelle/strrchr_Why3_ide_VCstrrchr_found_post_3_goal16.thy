theory strrchr_Why3_ide_VCstrrchr_found_post_3_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal16:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = t_1 a_3; x_1 :: int = l_strlen t_1 a_1; a_5 :: addr = shift a_1 x_1; x_2 :: int = t_1 (Mk_addr (0 :: int) (0 :: int)) in t_1 a = (0 :: int) \<longrightarrow> x = to_sint8 i \<longrightarrow> t_1 a_5 = (0 :: int) \<longrightarrow> shift a_1 ((1 :: int) + x_1) = shift a (1 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_lt a_2 a_4 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> is_sint8 (t_1 a_2) \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a a_5 \<longrightarrow> addr_le a_3 a_5 \<longrightarrow> addr_le a_4 a_5 \<longrightarrow> (if x = (0 :: int) then a_2 = a else Mk_addr (0 :: int) (0 :: int) = a_2) \<longrightarrow> ((\<exists>(a_6 :: addr). x = t_1 a_6 \<and> addr_le a_1 a_6 \<and> addr_lt a_6 a_5) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2) \<longrightarrow> \<not>x_2 = x \<or> \<not>addr_lt (Mk_addr (0 :: int) (0 :: int)) a \<or> \<not>addr_le a_1 (Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_6 a \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> \<not>x = t_1 a_6) \<longrightarrow> \<not>t_1 a_4 = x"
  sorry
end
