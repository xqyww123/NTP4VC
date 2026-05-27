theory parse_AttributeTypeAndValue_Why3_ide_VCparse_AttributeTypeAndValue_stmt_calls_parse_rdn_val_cn_p____goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift a_2 i_3; a_4 :: addr = shift___anonstruct__name_oid_11 (Mk_addr (-(8604 :: int)) (0 :: int)) i_2; x :: int = i_3 + i_4; a_5 :: addr = shift a_4 (2 :: int); a_6 :: addr = t_1 a_5 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i \<le> i_4 \<longrightarrow> x \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> i_2 \<le> (15 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x \<longrightarrow> x \<le> (65535 :: int) \<longrightarrow> x \<le> (2147483647 :: int) \<longrightarrow> i \<le> (2147483648 :: int) + i_4 \<longrightarrow> i_1 \<le> (65535 :: int) + i_3 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_1 \<longrightarrow> i_4 \<le> (65535 :: int) + i \<longrightarrow> i_4 \<le> (2147483647 :: int) + i \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t a_3 i_4) \<longrightarrow> a_6 = Mk_addr (8590 :: int) (0 :: int) \<or> a_6 = Mk_addr (8593 :: int) (0 :: int) \<or> a_6 = Mk_addr (8602 :: int) (0 :: int) \<or> a_6 = Mk_addr (8599 :: int) (0 :: int) \<or> a_6 = Mk_addr (8594 :: int) (0 :: int) \<or> a_6 = Mk_addr (8596 :: int) (0 :: int) \<or> a_6 = Mk_addr (8597 :: int) (0 :: int) \<or> a_6 = Mk_addr (8603 :: int) (0 :: int) \<or> a_6 = Mk_addr (8592 :: int) (0 :: int) \<or> a_6 = Mk_addr (8595 :: int) (0 :: int) \<or> a_6 = Mk_addr (8598 :: int) (0 :: int) \<or> a_6 = Mk_addr (8591 :: int) (0 :: int)"
  sorry
end
