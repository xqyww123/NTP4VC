theory strnchr_Why3_ide_VCstrnchr_not_exists_post_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal13:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  shows "let x :: int = t_1 a_1; x_1 :: int = offset a_1; x_2 :: int = offset a_2; x_3 :: int = i + x_2 - x_1; x_4 :: int = l_strnlen t_1 a_2 i; x_5 :: int = i + x_2; a_3 :: addr = shift a_2 x_4; x_6 :: int = to_sint8 i_1 in \<not>x = (0 :: int) \<longrightarrow> x_1 + l_strnlen t_1 a_1 x_3 = x_2 + x_4 \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_5 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a_2 i \<longrightarrow> is_uint64 x_3 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> (if x_5 = x_1 then Mk_addr (0 :: int) (0 :: int) = a else a_1 = a \<and> t_1 a = x_6) \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a_1 \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> \<not>t_1 a_4 = x_6) \<longrightarrow> (\<forall>(a_4 :: addr). addr_le a_2 a_4 \<longrightarrow> addr_lt a_4 a_3 \<longrightarrow> \<not>t_1 a_4 = x_6) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a"
  sorry
end
