theory strlcpy_Why3_ide_VCstrlcpy_disjoint_zero_size_size_is_greater_src_size_is_lo____goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = l_strlen t_1 a in \<not>x = x_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> (\<not>i = (0 :: int) \<or> i \<le> x_2) \<and> (\<not>i = (0 :: int) \<or> i \<le> (0 :: int) \<or> x_2 < i)"
  sorry
end
