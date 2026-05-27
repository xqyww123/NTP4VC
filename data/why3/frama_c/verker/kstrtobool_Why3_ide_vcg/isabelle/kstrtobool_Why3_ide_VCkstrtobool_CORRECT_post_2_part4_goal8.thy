theory kstrtobool_Why3_ide_VCkstrtobool_CORRECT_post_2_part4_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.Axiomatic5_Axiomatic5"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); x :: int = t_1 a_2; x_1 :: int = t_1 (shift a (1 :: int)) in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> p_kstrtobool_fmt_false t_1 a \<longrightarrow> p_kstrtobool_fmt t_1 a \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> valid_rd t a_2 (2 :: int) \<longrightarrow> x = (79 :: int) \<or> x = (111 :: int) \<longrightarrow> \<not>(x_1 = (78 :: int) \<or> x_1 = (110 :: int))"
  sorry
end
