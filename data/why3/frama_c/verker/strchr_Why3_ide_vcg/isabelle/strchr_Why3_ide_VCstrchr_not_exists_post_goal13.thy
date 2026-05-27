theory strchr_Why3_ide_VCstrchr_not_exists_post_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strchr_A_Strchr" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal13:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = to_sint8 i; x_1 :: int = t_1 a_1; a_3 :: addr = shift a_2 (l_strlen t_1 a_2); a_4 :: addr = shift a_2 (l_strlen t_2 a_2); x_2 :: int = t_2 a in l_strchr t_1 a_2 x = l_strchr t_1 a_1 x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> (if x_1 = x then a_1 = a \<and> t_2 = t_1 \<and> (a_4 = a \<longleftrightarrow> x_2 = (0 :: int)) \<and> (addr_lt a a_4 \<longleftrightarrow> \<not>x_2 = (0 :: int)) else t_3 = t_1 \<and> Mk_addr (0 :: int) (0 :: int) = a \<and> t_3 a_1 = (0 :: int)) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a_2 a_5 \<longrightarrow> \<not>t_1 a_5 = x) \<longrightarrow> (\<forall>(a_5 :: addr). addr_le a_2 a_5 \<longrightarrow> addr_le a_5 a_3 \<longrightarrow> \<not>t_1 a_5 = x) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a"
  sorry
end
