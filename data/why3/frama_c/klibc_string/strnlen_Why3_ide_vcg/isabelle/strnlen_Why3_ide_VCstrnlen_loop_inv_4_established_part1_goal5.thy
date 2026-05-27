theory strnlen_Why3_ide_VCstrnlen_loop_inv_4_established_part1_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_uint32 i"
  assumes fact5: "valid_rw t (shift a (0 :: int)) i"
  shows "addr_le a a"
  sorry
end
