theory fflush_Why3_ide_VCfflush_loop_inv_preserved_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  shows "let a_3 :: addr = shift a_2 (8 :: int); x :: int = t_1 a_3; a_4 :: addr = shift a_2 (0 :: int) in \<not>Mk_addr (1723 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (0 :: int) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_4 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_2 \<longrightarrow> p_valid_io_file_pvt t t_2 (t_1(shift a_2 (7 :: int) := i_3, shift a_4 (1 :: int) := i_2, shift a_4 (2 :: int) := i_1, a_3 := i)) (t_2 (shift a_2 (4 :: int)))"
  sorry
end
