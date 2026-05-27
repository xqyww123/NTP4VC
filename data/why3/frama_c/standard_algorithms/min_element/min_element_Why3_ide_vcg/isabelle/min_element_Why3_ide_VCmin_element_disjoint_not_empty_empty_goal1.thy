theory min_element_Why3_ide_VCmin_element_disjoint_not_empty_empty_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_min_element_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 (0 :: int)"
  assumes fact3: "valid_rd t (shift a (0 :: int)) (0 :: int)"
  shows "\<not>True \<or> (0 :: int) \<le> (0 :: int)"
  sorry
end
