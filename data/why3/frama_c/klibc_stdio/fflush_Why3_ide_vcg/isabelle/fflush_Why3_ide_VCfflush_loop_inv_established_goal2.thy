theory fflush_Why3_ide_VCfflush_loop_inv_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal2:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  assumes fact0: "region (0 :: int) \<le> (0 :: int)"
  assumes fact1: "framed t_2"
  assumes fact2: "linked t"
  assumes fact3: "p_valid_io_file_pvt t t_2 t_1 a"
  assumes fact4: "p_valid_io_file_pvt t t_2 t_1 a_1"
  shows "p_valid_io_file_pvt t t_2 t_1 (t_2 (shift (Mk_addr (1723 :: int) (0 :: int)) (4 :: int)))"
  sorry
end
