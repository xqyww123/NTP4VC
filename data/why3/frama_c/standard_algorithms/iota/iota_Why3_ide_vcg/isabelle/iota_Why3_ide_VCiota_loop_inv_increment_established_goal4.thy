theory iota_Why3_ide_VCiota_loop_inv_increment_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_iota_lib.Compound_Compound" "frama_c_standard_algorithms_iota_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "i + i_1 \<le> (2147483647 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "is_sint32 i"
  assumes fact5: "valid_rw t (shift a (0 :: int)) i_1"
  shows "p_iota t_1 a (0 :: int) i"
  sorry
end
