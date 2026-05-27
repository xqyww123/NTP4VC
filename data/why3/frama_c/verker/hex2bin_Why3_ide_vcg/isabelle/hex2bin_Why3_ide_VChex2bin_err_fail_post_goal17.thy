theory hex2bin_Why3_ide_VChex2bin_err_fail_post_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal17:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  shows "let x :: int = offset a; x_1 :: int = offset a_1; a_4 :: addr = shift a_1 (0 :: int) in (x - x_1) cdiv (2 :: int) = (0 :: int) \<longrightarrow> (x_1 - x) cmod (2 :: int) = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> \<not>p_isxdigit (t_1 a_3) \<longrightarrow> addr_lt a_3 a_4 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) (1 :: int) \<longrightarrow> \<not>(\<forall>(a_5 :: addr). addr_lt a_5 a \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> p_isxdigit (t_1 a_5))"
  sorry
end
