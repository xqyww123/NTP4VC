theory parse_ia5_string_Why3_ide_VCparse_ia5_string_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> t_1 a_1 = (22 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483646 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i \<le> (65537 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint8 (t_1 a_2) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_1 i) \<longrightarrow> valid_rd t a_2 (1 :: int)"
  sorry
end
