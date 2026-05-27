theory fflush_Why3_ide_VCfflush_loop_inv_2_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal5:
  shows "let a :: addr = Mk_addr (1723 :: int) (0 :: int) in \<forall>(t :: int \<Rightarrow> int) (t_1 :: addr \<Rightarrow> int) (t_2 :: addr \<Rightarrow> addr) (a_2 :: addr) (a_1 :: addr). region (0 :: int) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_2 \<longrightarrow> \<not>t_2 (shift a (4 :: int)) = a"
  sorry
end
