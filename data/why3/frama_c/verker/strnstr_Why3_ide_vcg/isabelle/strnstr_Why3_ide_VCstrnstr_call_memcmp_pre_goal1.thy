theory strnstr_Why3_ide_VCstrnstr_call_memcmp_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> i_1 \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> \<not>(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> \<not>t_1 (shift a i_2) = (0 :: int))"
  sorry
end
