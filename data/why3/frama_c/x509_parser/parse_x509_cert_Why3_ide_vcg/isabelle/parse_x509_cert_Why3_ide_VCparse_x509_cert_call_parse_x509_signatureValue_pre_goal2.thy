theory parse_x509_cert_Why3_ide_VCparse_x509_cert_call_parse_x509_signatureValue_pre_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; a_2 :: addr = shift a_1 i_2; a_3 :: addr = shift a_1 (i_1 - i); a_4 :: addr = shift a_1 (i_1 + i_3 - i); x_2 :: int = i - i_3; x_4 :: int = i_1 - i_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = i_1 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = base a \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 < i \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_3 \<longrightarrow> i \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_1 \<le> (65535 :: int) + i_2 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_2 \<longrightarrow> i_2 \<le> (2147483648 :: int) + i_1 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i \<longrightarrow> (2 :: int) + i + i_2 \<le> i_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 x_2 \<longrightarrow> is_uint16 x_4 \<longrightarrow> is_uint16 (i_1 - i - i_2) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> (i_2 < i_1 \<longrightarrow> valid_rd t a_2 x_4) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> valid_rd t a_4 x_2"
  sorry
end
