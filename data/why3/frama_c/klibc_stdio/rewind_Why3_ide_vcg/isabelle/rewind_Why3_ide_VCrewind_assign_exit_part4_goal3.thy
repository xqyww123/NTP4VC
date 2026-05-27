theory rewind_Why3_ide_VCrewind_assign_exit_part4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal3:
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_6 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  fixes a_10 :: "addr"
  fixes a_7 :: "addr"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  shows "let a_11 :: addr = shift a_2 (0 :: int); a_12 :: addr = shift a_4 (8 :: int) in a_11 = shift a (0 :: int) \<longrightarrow> shift a_6 (0 :: int) = a_11 \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_5 \<longrightarrow> \<not>invalid t a_12 (1 :: int) \<longrightarrow> p_valid_file t t_1 a_11 \<longrightarrow> a_12 = shift a_10 (7 :: int) \<or> shift a_7 (8 :: int) = a_12 \<or> shift a_11 (1 :: int) = a_12 \<or> shift (shift a_9 (0 :: int)) (1 :: int) = a_12 \<or> shift a_11 (2 :: int) = a_12 \<or> shift (shift a_8 (0 :: int)) (2 :: int) = a_12"
  sorry
end
