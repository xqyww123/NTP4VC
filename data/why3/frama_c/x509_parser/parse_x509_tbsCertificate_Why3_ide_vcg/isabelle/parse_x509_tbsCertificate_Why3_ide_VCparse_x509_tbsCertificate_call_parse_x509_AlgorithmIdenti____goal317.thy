theory parse_x509_tbsCertificate_Why3_ide_VCparse_x509_tbsCertificate_call_parse_x509_AlgorithmIdenti____goal317
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal317:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 i; a_4 :: addr = shift a_2 (i + i_1 - i_2); a_5 :: addr = shift a_2 (i + i_1 + i_3 - i_2); x_4 :: int = i_2 - i_3 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>a_1 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 < i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i \<le> i_4 \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i + i_1 \<le> i_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i_2 \<le> (65535 :: int) \<longrightarrow> i_2 \<le> (2147483647 :: int) \<longrightarrow> i_2 \<le> (65535 :: int) + i_3 \<longrightarrow> i_2 \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_2 \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_uint16 (i_1 - i_2) \<longrightarrow> is_uint16 x_4 \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_4) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_3 i_1) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t a_4 i_2) \<longrightarrow> valid_rd t a_5 x_4"
  sorry
end
