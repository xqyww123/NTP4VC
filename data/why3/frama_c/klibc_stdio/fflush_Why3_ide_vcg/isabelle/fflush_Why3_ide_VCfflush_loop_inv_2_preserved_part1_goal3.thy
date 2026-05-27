theory fflush_Why3_ide_VCfflush_loop_inv_2_preserved_part1_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal3:
  shows "let a :: addr = Mk_addr (1723 :: int) (0 :: int) in \<forall>(i :: int) (t :: int \<Rightarrow> int) (t_1 :: addr \<Rightarrow> int) (t_2 :: addr \<Rightarrow> addr) (a_3 :: addr) (a_2 :: addr) (a_1 :: addr). let x :: int = t_1 (shift a_3 (8 :: int)) in \<not>a = a_3 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (0 :: int) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_2 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> \<not>t_2 (shift a_3 (4 :: int)) = a"
  sorry
end
