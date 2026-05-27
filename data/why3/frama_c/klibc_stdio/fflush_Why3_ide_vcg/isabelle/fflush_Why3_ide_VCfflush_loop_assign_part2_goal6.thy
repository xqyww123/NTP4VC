theory fflush_Why3_ide_VCfflush_loop_assign_part2_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  shows "let x :: int = t_1 (shift a_2 (8 :: int)) in \<not>Mk_addr (1723 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (0 :: int) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> \<not>p_valid_io_file_pvt t t_2 t_1 a_2"
  sorry
end
