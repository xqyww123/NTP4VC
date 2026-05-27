theory min_element_Why3_ide_VCmin_element_complete_not_empty_empty_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_min_element_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "valid_rd t (shift a (0 :: int)) i"
  shows "i = (0 :: int) \<or> (0 :: int) < i"
  sorry
end
