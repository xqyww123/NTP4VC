theory bufs_differ_Why3_ide_VCbufs_differ_loop_inv_established_part2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint16 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  assumes fact5: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "(0 :: int) \<le> i"
  sorry
end
