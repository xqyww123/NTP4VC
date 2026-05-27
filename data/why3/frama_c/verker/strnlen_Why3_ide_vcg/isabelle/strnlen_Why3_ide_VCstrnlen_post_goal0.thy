theory strnlen_Why3_ide_VCstrnlen_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_3 :: int = i + x_1 - x; x_4 :: int = l_strnlen t_1 a_1 x_3 in x + x_4 = x_1 + l_strnlen t_1 a i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> is_uint64 x_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> i = (0 :: int) \<or> t_1 a = (0 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> x_4 = to_uint64 (x_1 - x)"
  sorry
end
