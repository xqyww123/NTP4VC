theory skip_spaces_Why3_ide_VCskip_spaces_post_6_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal5:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  shows "let x :: int = t_2 a in region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 (t_3 a) \<longrightarrow> \<not>p_isspace x \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_2 a_1)) \<longrightarrow> (\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> p_isspace (t_2 a_2)) \<longrightarrow> p_valid_str t_1 t_3 a"
  sorry
end
