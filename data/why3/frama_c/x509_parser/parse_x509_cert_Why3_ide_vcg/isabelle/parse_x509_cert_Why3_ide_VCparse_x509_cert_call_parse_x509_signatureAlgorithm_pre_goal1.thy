theory parse_x509_cert_Why3_ide_VCparse_x509_cert_call_parse_x509_signatureAlgorithm_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = i_1 + i_2; a_2 :: addr = shift a x; x_1 :: int = (2147483648 :: int) + i; x_3 :: int = i - i_1; x_4 :: int = i - i_1 - i_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>a_1 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> x < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> i \<le> (65535 :: int) + i_1 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> x_1 \<longrightarrow> x \<le> x_1 \<longrightarrow> i \<le> (65535 :: int) + i_1 + i_2 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint16 x_4 \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a (0 :: int)) i) \<longrightarrow> (i_1 < i \<longrightarrow> valid_rd t a_1 x_3) \<longrightarrow> valid_rd t a_2 x_4"
  sorry
end
