theory parse_rdn_val_dc_Why3_ide_VCparse_rdn_val_dc_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal0:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "\<not>i = (0 :: int)"
  assumes fact1: "\<not>Mk_addr (0 :: int) (0 :: int) = a"
  assumes fact2: "(0 :: int) \<le> i"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "-(2147483646 :: int) \<le> i"
  assumes fact5: "(2 :: int) \<le> i"
  assumes fact6: "(3 :: int) \<le> i"
  assumes fact7: "i \<le> (65 :: int)"
  assumes fact8: "i \<le> (65537 :: int)"
  assumes fact9: "linked t"
  assumes fact10: "is_uint16 i"
  assumes fact11: "(0 :: int) < i \<longrightarrow> valid_rd t (shift a (0 :: int)) i"
  shows "valid_rd t (shift a (2 :: int)) (1 :: int)"
  sorry
end
