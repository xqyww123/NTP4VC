theory check_visible_string_Why3_ide_VCcheck_visible_string_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "\<not>i_1 = (0 :: int)"
  assumes fact1: "\<not>Mk_addr (0 :: int) (0 :: int) = a"
  assumes fact2: "i < i_1"
  assumes fact3: "(0 :: int) \<le> i_1"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint16 i"
  assumes fact7: "is_uint16 i_1"
  assumes fact8: "(0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1"
  shows "valid_rd t (shift a i) (1 :: int)"
  sorry
end
