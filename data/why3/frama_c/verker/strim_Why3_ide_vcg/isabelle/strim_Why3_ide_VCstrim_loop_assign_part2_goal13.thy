theory strim_Why3_ide_VCstrim_loop_assign_part2_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal13:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a; x_1 :: int = t_1 a_1; a_2 :: addr = shift a (x - (1 :: int)); x_2 :: int = t_1 a_2 in \<not>x = (0 :: int) \<longrightarrow> (p_isspace x_1 \<longleftrightarrow> \<not>i = (0 :: int)) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> addr_le (shift a (-(1 :: int))) a_1 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> \<not>(\<forall>(a_3 :: addr). addr_lt a_1 a_3 \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_isspace (t_1 a_3))"
  sorry
end
