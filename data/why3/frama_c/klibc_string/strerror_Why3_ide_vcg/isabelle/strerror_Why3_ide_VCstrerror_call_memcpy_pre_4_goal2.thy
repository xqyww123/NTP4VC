theory strerror_Why3_ide_VCstrerror_call_memcpy_pre_4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal2:
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  assumes fact0: "to_uint32 (i_1 cdiv (10 :: int)) = (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "sconst t_2"
  assumes fact3: "is_uint32 i_1"
  shows "valid_rw t_1 (shift a (-(1 :: int))) (to_uint32 i)"
  sorry
end
