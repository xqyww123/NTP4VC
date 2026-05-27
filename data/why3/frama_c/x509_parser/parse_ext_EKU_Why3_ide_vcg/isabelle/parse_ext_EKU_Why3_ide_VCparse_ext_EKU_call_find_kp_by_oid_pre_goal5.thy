theory parse_ext_EKU_Why3_ide_VCparse_ext_EKU_call_find_kp_by_oid_pre_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_3 :: addr = shift a_2 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = i_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (3 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> (2147483647 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> valid_rw t a (15 :: int) \<longrightarrow> is_uint16 (i_2 - i_3) \<longrightarrow> valid_rd t a_3 i \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2) \<longrightarrow> valid_rd t a_3 i_1"
  sorry
end
