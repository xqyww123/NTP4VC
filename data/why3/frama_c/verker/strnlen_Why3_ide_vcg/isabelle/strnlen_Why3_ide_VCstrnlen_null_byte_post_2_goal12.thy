theory strnlen_Why3_ide_VCstrnlen_null_byte_post_2_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal12:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a; x_1 :: int = offset a_1; x_2 :: int = i_2 + x_1 - x; x_3 :: int = l_strnlen t_1 a_1 i_2; x_4 :: int = i_2 + x_1; x_5 :: int = to_uint64 (x - x_1) in t_1 (shift a_1 i) = (0 :: int) \<longrightarrow> x + l_strnlen t_1 a x_2 = x_1 + x_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_2 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> x_4 \<longrightarrow> i_1 < x_5 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_strn t t_1 a_1 i_2 \<longrightarrow> is_uint64 x_2 \<longrightarrow> addr_le a (shift a_1 x_3) \<longrightarrow> p_valid_strn t t_1 a x_2 \<longrightarrow> is_sint8 (t_1 (shift a_1 x_5)) \<longrightarrow> t_1 a = (0 :: int) \<or> x_4 = x \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_1 < x \<longrightarrow> \<not>t_1 (shift a_1 i_3) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)"
  sorry
end
