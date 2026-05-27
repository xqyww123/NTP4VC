theory memchr_Why3_ide_VCmemchr_loop_inv_2_established_part2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "-(128 :: int) \<le> i_1"
  assumes fact3: "i_1 \<le> (127 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "sconst t_1"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_sint32 i_1"
  assumes fact8: "valid_rw t (shift a (0 :: int)) i"
  shows "addr_le a (shift a i)"
  sorry
end
