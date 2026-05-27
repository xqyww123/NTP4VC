theory fclose_Why3_ide_VCfclose_call_fflush_pre_2_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal14:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  assumes fact0: "shift a_2 (0 :: int) = shift a (0 :: int)"
  assumes fact1: "region (base a_2) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  assumes fact4: "p_valid_io_file_pvt t t_2 t_1 a_1"
  assumes fact5: "p_valid_io_file_pvt t t_2 t_1 a_3"
  shows "p_valid_io_file_pvt t t_2 t_1 a_4"
  sorry
end
