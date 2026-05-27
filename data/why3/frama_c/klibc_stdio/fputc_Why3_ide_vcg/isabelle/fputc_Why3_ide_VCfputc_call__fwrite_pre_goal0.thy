theory fputc_Why3_ide_VCfputc_call__fwrite_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "framed t_1"
  assumes fact2: "linked t"
  shows "shift a (0 :: int) = a_1"
  sorry
end
