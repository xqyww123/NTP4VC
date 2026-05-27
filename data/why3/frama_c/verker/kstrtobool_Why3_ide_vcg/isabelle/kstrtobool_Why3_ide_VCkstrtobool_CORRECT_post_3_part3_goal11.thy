theory kstrtobool_Why3_ide_VCkstrtobool_CORRECT_post_3_part3_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.Axiomatic5_Axiomatic5"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a (1 :: int)); a_2 :: addr = shift a (0 :: int); x_1 :: int = t_1 a_2 in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>x = (70 :: int) \<longrightarrow> \<not>x = (78 :: int) \<longrightarrow> \<not>x = (102 :: int) \<longrightarrow> \<not>x = (110 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> p_kstrtobool_fmt t_1 a \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x \<longrightarrow> valid_rd t a_2 (2 :: int) \<longrightarrow> \<not>(x_1 = (79 :: int) \<or> x_1 = (111 :: int))"
  sorry
end
