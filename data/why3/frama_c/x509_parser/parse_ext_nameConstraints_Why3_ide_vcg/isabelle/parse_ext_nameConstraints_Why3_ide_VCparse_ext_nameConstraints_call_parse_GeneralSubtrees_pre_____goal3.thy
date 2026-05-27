theory parse_ext_nameConstraints_Why3_ide_VCparse_ext_nameConstraints_call_parse_GeneralSubtrees_pre_____goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes i_5 :: "int"
  fixes i_2 :: "int"
  fixes i_7 :: "int"
  fixes i_6 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_3; x_2 :: int = i_1 + i_4; a_3 :: addr = shift a_1 (i_3 + i_4); a_4 :: addr = shift a_1 (i + i_3 - i_1); a_5 :: addr = shift a_1 (i + i_3 + i_5 - i_1); x_5 :: int = i - i_1 - i_4 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_7 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x_2 = i \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i_6 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_5 \<le> i_1 \<longrightarrow> i_6 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> x_2 \<le> i \<longrightarrow> i_5 + i_6 \<le> i_1 \<longrightarrow> i + i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> (2 :: int) \<le> i_5 \<longrightarrow> i_1 \<le> (65535 :: int) \<longrightarrow> i_1 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_4 \<longrightarrow> i \<le> (2147483647 :: int) + i_4 \<longrightarrow> i_1 \<le> (65535 :: int) + i_5 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_5 \<longrightarrow> i_4 \<le> (2147483648 :: int) + i \<longrightarrow> i_5 \<le> (2147483648 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_uint16 i_6 \<longrightarrow> is_sint32 i_7 \<longrightarrow> valid_rw t a (15 :: int) \<longrightarrow> is_uint16 (i - i_4) \<longrightarrow> is_uint16 x_5 \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_2 i) \<longrightarrow> (x_2 < i \<longrightarrow> valid_rd t a_3 x_5) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_4 i_1) \<longrightarrow> valid_rd t a_5 i_6"
  sorry
end
