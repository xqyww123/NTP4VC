theory fread_Why3_ide_VCfread_call__fread_pre_2_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "region (base a_2) \<le> (0 :: int)"
  assumes fact2: "framed t_1"
  assumes fact3: "linked t"
  assumes fact4: "is_uint32 i"
  assumes fact5: "is_uint32 i_1"
  shows "separated (shift a_1 (0 :: int)) (to_uint32 (i * i_1)) (t_1 (shift a (4 :: int))) (11 :: int)"
  sorry
end
