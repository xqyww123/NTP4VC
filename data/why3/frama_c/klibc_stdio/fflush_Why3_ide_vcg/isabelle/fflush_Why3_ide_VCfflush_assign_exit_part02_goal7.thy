theory fflush_Why3_ide_VCfflush_assign_exit_part02_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal7:
  fixes a_2 :: "addr"
  fixes a_8 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_7 :: "addr"
  fixes a_4 :: "addr"
  fixes a_6 :: "addr"
  fixes a_5 :: "addr"
  shows "let a_9 :: addr = shift a_2 (0 :: int); a_10 :: addr = shift a_8 (7 :: int) in \<not>a_9 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> a_9 = shift a (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_8 \<longrightarrow> \<not>invalid t a_10 (1 :: int) \<longrightarrow> a_10 = shift a_7 (7 :: int) \<or> shift a_4 (8 :: int) = a_10 \<or> shift (shift a_6 (0 :: int)) (1 :: int) = a_10 \<or> shift (shift a_5 (0 :: int)) (2 :: int) = a_10"
  sorry
end
