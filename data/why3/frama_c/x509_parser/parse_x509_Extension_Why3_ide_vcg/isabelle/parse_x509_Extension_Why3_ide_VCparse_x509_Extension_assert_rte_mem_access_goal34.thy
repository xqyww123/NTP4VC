theory parse_x509_Extension_Why3_ide_VCparse_x509_Extension_assert_rte_mem_access_goal34
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal34:
  fixes a_3 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = shift a_3 i_3; a_5 :: addr = shift a_3 (i + i_3); x :: int = i_3 + i_4; x_1 :: int = i_4 - i in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>i_4 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_3 \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>shift___anonstruct__ext_oid_14 (Mk_addr (-(8682 :: int)) (0 :: int)) i_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i \<le> i_4 \<longrightarrow> x \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> i_2 \<le> (28 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x \<longrightarrow> x \<le> (65535 :: int) \<longrightarrow> x \<le> (2147483647 :: int) \<longrightarrow> i \<le> (2147483648 :: int) + i_4 \<longrightarrow> i_1 \<le> (65535 :: int) + i_3 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_1 \<longrightarrow> (3 :: int) + i \<le> i_4 \<longrightarrow> i_4 \<le> (65535 :: int) + i \<longrightarrow> i_4 \<le> (2147483647 :: int) + i \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (15 :: int) \<longrightarrow> is_uint16 x_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) (29 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_3 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_4 i) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t a_4 i_4) \<longrightarrow> (i < i_4 \<longrightarrow> valid_rd t a_5 x_1) \<longrightarrow> valid_rd t (shift a_3 ((2 :: int) + i + i_3)) (1 :: int)"
  sorry
end
