theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_inv_3_established_part2_goal32
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal32:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i_1"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "framed t_3"
  assumes fact4: "linked t"
  assumes fact5: "sconst t_2"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "p_valid_io_file_pvt t t_3 t_1 a"
  assumes fact9: "valid_rw t (shift a_1 (0 :: int)) i_1"
  shows "(0 :: int) \<le> i"
  sorry
end
