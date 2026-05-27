theory parse_x509_subjectPublicKeyInfo_Why3_ide_VCparse_x509_subjectPublicKeyInfo_assert_rte_mem_access_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_3; m :: int \<Rightarrow> int = t(7106 :: int := 4 :: int); a_3 :: addr = t_1 i_2; a_4 :: addr = shift a_1 (0 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i \<le> i_4 \<longrightarrow> i_3 + i_4 \<le> i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint8 i_2 \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rd m a_3 (8 :: int) \<longrightarrow> separated a_2 (1 :: int) (Mk_addr (7106 :: int) (0 :: int)) (4 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_4 i_1) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd m a_4 i_1) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd m a_2 i_4) \<longrightarrow> valid_rd m (shift a_3 (4 :: int)) (1 :: int)"
  sorry
end
