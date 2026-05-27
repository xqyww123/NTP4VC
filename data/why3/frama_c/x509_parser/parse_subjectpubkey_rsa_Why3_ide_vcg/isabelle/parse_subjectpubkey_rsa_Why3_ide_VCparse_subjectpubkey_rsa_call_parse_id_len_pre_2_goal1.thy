theory parse_subjectpubkey_rsa_Why3_ide_VCparse_subjectpubkey_rsa_call_parse_id_len_pre_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; a_3 :: addr = shift a (1 :: int); a_4 :: addr = shift a_1 ((1 :: int) + i_1); x :: int = i_2 - (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> t_2 a_3 = shift (Mk_addr (-(8561 :: int)) (0 :: int)) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> i_1 + i_2 \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(2147483647 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (65536 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i) \<longrightarrow> valid_rd t a_4 x"
  sorry
end
