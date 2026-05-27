theory find_curve_by_oid_Why3_ide_VCfind_curve_by_oid_call_bufs_differ_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes t_1 :: "int \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = t_1 i; a_2 :: addr = shift a_1 (3 :: int); x :: int = t_2 a_2; a_3 :: addr = shift a (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> i \<le> (5 :: int) \<longrightarrow> i \<le> (6 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> is_uint8 x \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t (shift a_1 (2 :: int)) (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> ((0 :: int) < x \<longrightarrow> valid_rd t a_3 x) \<longrightarrow> valid_rd t a_3 x"
  sorry
end
