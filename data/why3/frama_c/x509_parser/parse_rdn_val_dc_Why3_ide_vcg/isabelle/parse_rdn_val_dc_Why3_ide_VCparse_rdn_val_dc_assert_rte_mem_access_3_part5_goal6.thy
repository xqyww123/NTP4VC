theory parse_rdn_val_dc_Why3_ide_VCparse_rdn_val_dc_assert_rte_mem_access_3_part5_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal6:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (4 :: int) + i_1; x_1 :: int = i - (4 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i = (3 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483646 :: int) \<le> i \<longrightarrow> -(2147483645 :: int) \<le> i \<longrightarrow> -(2147483644 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> (4 :: int) \<le> i \<longrightarrow> i \<le> (65 :: int) \<longrightarrow> i \<le> (65537 :: int) \<longrightarrow> i \<le> (65538 :: int) \<longrightarrow> i \<le> (65539 :: int) \<longrightarrow> x \<le> i \<longrightarrow> (5 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_uint16 x_1 \<longrightarrow> is_uint16 (i - (3 :: int)) \<longrightarrow> is_uint16 (i - (2 :: int)) \<longrightarrow> valid_rd t (shift a (2 :: int)) (1 :: int) \<longrightarrow> valid_rd t (shift a ((3 :: int) + to_sint32 x_1)) (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a (0 :: int)) i) \<longrightarrow> valid_rd t (shift a x) (1 :: int)"
  sorry
end
