theory count_Why3_ide_VCcount_loop_inv_bound_established_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_count_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "valid_rd t (shift a (0 :: int)) i"
  shows "(0 :: int) \<le> i"
  sorry
end
