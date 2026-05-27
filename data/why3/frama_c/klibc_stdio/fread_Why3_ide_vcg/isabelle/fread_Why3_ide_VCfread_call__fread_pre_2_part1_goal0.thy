theory fread_Why3_ide_VCfread_call__fread_pre_2_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  assumes fact0: "region (base a_2) \<le> (0 :: int)"
  assumes fact1: "region (base a_3) \<le> (0 :: int)"
  assumes fact2: "framed t_1"
  assumes fact3: "linked t"
  shows "separated (t_1 (shift a_1 (4 :: int))) (11 :: int) (t_1 (shift a (3 :: int))) (11 :: int)"
  sorry
end
