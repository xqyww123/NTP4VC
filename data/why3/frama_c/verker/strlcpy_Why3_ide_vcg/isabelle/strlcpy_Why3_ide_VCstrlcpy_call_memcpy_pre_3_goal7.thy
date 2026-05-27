theory strlcpy_Why3_ide_VCstrlcpy_call_memcpy_pre_3_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = l_strlen t_1 a in \<not>i = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> t_1 (shift a x_2) = (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> (if i \<le> x_2 then to_uint64 (i - (1 :: int)) = i_1 else x_2 = i_1) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_2 \<longrightarrow> \<not>t_1 (shift a i_2) = (0 :: int)) \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1"
  sorry
end
