theory parse_x509_subjectPublicKeyInfo_Why3_ide_VCparse_x509_subjectPublicKeyInfo_call_parse_id_len_pre_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) < i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd (t(7106 :: int := 4 :: int)) a_2 i"
  sorry
end
