theory parse_AttributeTypeAndValue_Why3_ide_VCparse_AttributeTypeAndValue_call_parse_rdn_val_pseudo_pre_goal26
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal26:
  fixes a_2 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift a_2 i_3; x :: int = i + i_4; a_4 :: addr = shift___anonstruct__name_oid_11 (Mk_addr (-(8604 :: int)) (0 :: int)) i_2; a_5 :: addr = shift a_2 (i + i_3); a_6 :: addr = shift a_4 (2 :: int); x_1 :: int = i + i_3 + i_4 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_6 = Mk_addr (8603 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i_4 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> x \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> -(2147483648 :: int) \<le> i_4 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> i_2 \<le> (15 :: int) \<longrightarrow> i_4 \<le> (65535 :: int) \<longrightarrow> i_4 \<le> (2147483647 :: int) \<longrightarrow> i_1 \<le> (65535 :: int) + i_3 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_1 \<longrightarrow> -(2147483648 :: int) \<le> x_1 \<longrightarrow> x_1 \<le> (65535 :: int) \<longrightarrow> x_1 \<le> (2147483647 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> ((0 :: int) < x \<longrightarrow> valid_rd t a_3 x) \<longrightarrow> valid_rd t a_5 i_4"
  sorry
end
