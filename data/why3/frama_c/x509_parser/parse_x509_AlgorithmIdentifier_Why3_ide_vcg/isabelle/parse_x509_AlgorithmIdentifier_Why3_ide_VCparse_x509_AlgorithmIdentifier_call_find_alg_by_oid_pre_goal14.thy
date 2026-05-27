theory parse_x509_AlgorithmIdentifier_Why3_ide_VCparse_x509_AlgorithmIdentifier_call_find_alg_by_oid_pre_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal14:
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = shift a_2 i_2 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>a_2 = a_1 \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i \<le> i_3 \<longrightarrow> i_2 + i_3 \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> valid_rw t a (4 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> separated a (4 :: int) a_1 (1 :: int) \<longrightarrow> separated a_2 (1 :: int) a (4 :: int) \<longrightarrow> separated a_3 (1 :: int) a (4 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t a_4 i_3) \<longrightarrow> valid_rd t a_4 i"
  sorry
end
