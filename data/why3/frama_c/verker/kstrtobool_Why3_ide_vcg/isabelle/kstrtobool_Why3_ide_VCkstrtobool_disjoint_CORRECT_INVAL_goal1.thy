theory kstrtobool_Why3_ide_VCkstrtobool_disjoint_CORRECT_INVAL_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.Axiomatic5_Axiomatic5"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 (t_1 a_2) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a \<or> valid_rd t a_2 (2 :: int) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a \<or> \<not>p_kstrtobool_fmt t_1 a \<or> \<not>Mk_addr (0 :: int) (0 :: int) = a \<and> p_kstrtobool_fmt t_1 a"
  sorry
end
