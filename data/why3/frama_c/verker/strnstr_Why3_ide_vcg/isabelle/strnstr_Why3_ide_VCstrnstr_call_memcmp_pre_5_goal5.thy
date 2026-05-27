theory strnstr_Why3_ide_VCstrnstr_call_memcmp_pre_5_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_5 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let x :: int = l_strlen t_1 a_4 in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a_4 x) = (0 :: int) \<longrightarrow> i_1 \<le> i \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> is_uint64 x \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> \<not>t_1 (shift a_4 i_2) = (0 :: int)) \<longrightarrow> base a_3 = base a_2 \<longleftrightarrow> base a_1 = base a"
  sorry
end
