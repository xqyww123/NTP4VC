theory find_curve_by_oid_Why3_ide_VCfind_curve_by_oid_post_part4_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_1 :: "int \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = t_1 i; a_2 :: addr = shift a_1 (3 :: int); x :: int = t_2 a_2; a_3 :: addr = shift a_1 (2 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>a_1 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> i \<le> (5 :: int) \<longrightarrow> i \<le> (6 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> is_uint8 x \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t (shift a (0 :: int)) x \<longrightarrow> valid_rd t (shift (t_3 a_3) (0 :: int)) x \<longrightarrow> (\<exists>(i_1 :: int). a_1 = t_1 i_1 \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> (5 :: int))"
  sorry
end
