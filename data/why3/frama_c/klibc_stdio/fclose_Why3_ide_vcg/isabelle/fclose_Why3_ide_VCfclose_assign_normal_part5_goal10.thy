theory fclose_Why3_ide_VCfclose_assign_normal_part5_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal10:
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes a_10 :: "addr"
  fixes a_7 :: "addr"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  fixes a_11 :: "addr"
  fixes a_12 :: "addr"
  shows "let a_13 :: addr = shift a_2 (0 :: int); a_14 :: addr = shift (shift a_4 (0 :: int)) (2 :: int) in a_13 = shift a (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_5 \<longrightarrow> \<not>invalid t a_14 (1 :: int) \<longrightarrow> a_13 = Mk_addr (0 :: int) (0 :: int) \<or> shift a_6 (0 :: int) = a_13 \<longrightarrow> a_14 = shift a_10 (7 :: int) \<or> a_14 = shift a_7 (8 :: int) \<or> a_14 = shift (shift a_9 (0 :: int)) (1 :: int) \<or> shift (shift a_8 (0 :: int)) (2 :: int) = a_14 \<or> shift (t_2 (shift a_11 (3 :: int))) (4 :: int) = a_14 \<or> shift (t_2 (shift a_12 (4 :: int))) (3 :: int) = a_14"
  sorry
end
