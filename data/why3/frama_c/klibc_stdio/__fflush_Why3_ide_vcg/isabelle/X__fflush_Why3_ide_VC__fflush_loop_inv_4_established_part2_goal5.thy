theory X__fflush_Why3_ide_VC__fflush_loop_inv_4_established_part2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "t_1 (shift a (7 :: int)) = (0 :: int)"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  assumes fact4: "p_valid_io_file_pvt t t_2 t_1 a"
  shows "base (t_2 (shift a (6 :: int))) = base (t_2 (shift a (5 :: int)))"
  sorry
end
