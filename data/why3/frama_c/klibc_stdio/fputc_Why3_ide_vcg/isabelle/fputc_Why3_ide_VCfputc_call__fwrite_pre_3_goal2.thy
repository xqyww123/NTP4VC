theory fputc_Why3_ide_VCfputc_call__fwrite_pre_3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Globals_Globals"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "framed t_1"
  assumes fact2: "linked t"
  shows "valid_rw (t(20235 :: int := 1 :: int)) (shift a (0 :: int)) (1 :: int)"
  sorry
end
