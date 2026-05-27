theory fflush_Why3_ide_VCfflush_loop_inv_preserved_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  assumes fact0: "\<not>Mk_addr (1723 :: int) (0 :: int) = a_2"
  assumes fact1: "t_1 (shift a_2 (8 :: int)) = (0 :: int)"
  assumes fact2: "region (0 :: int) \<le> (0 :: int)"
  assumes fact3: "framed t_2"
  assumes fact4: "linked t"
  assumes fact5: "p_valid_io_file_pvt t t_2 t_1 a"
  assumes fact6: "p_valid_io_file_pvt t t_2 t_1 a_1"
  assumes fact7: "p_valid_io_file_pvt t t_2 t_1 a_2"
  shows "p_valid_io_file_pvt t t_2 t_1 (t_2 (shift a_2 (4 :: int)))"
  sorry
end
