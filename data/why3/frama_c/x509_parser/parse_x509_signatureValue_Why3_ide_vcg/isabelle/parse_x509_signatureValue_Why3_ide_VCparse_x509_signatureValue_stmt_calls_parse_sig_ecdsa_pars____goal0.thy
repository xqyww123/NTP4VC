theory parse_x509_signatureValue_Why3_ide_VCparse_x509_signatureValue_stmt_calls_parse_sig_ecdsa_pars____goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Globals_Globals"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift a (5 :: int); a_4 :: addr = t_1 a_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rd t a (8 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i) \<longrightarrow> a_4 = Mk_addr (8418 :: int) (0 :: int) \<or> a_4 = Mk_addr (8423 :: int) (0 :: int)"
  sorry
end
