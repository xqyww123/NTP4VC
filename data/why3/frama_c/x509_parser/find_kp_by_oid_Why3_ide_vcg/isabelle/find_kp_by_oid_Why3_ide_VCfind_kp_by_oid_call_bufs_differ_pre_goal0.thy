theory find_kp_by_oid_Why3_ide_VCfind_kp_by_oid_call_bufs_differ_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift___anonstruct__kp_oid_13 (Mk_addr (-(8645 :: int)) (0 :: int)) i; a_3 :: addr = shift a_2 (1 :: int); x :: int = t_1 a_3; a_4 :: addr = shift a_1 (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> i \<le> (6 :: int) \<longrightarrow> i \<le> (7 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> is_uint8 x \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> ((0 :: int) < x \<longrightarrow> valid_rd t a_4 x) \<longrightarrow> valid_rd t a_4 x"
  sorry
end
