theory strsep_Why3_ide_VCstrsep_disjoint_input_strpbrk_not_null_input_strpbrk_null____goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn"
begin
theorem goal1:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = t_2 a; a_3 :: addr = l_strpbrk a_2 a_1 in (\<not>p_valid_str t t_1 a_2 \<longleftrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int)) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> (\<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<or> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<or> \<not>p_valid_str t t_1 a_2) \<and> (\<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<or> a_3 = Mk_addr (0 :: int) (0 :: int) \<or> \<not>p_valid_str t t_1 a_2)"
  sorry
end
