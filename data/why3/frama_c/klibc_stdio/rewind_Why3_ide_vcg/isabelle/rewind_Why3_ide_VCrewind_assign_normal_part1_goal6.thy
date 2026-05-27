theory rewind_Why3_ide_VCrewind_assign_normal_part1_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes a_2 :: "addr"
  fixes a_5 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a_9 :: "addr"
  fixes a_6 :: "addr"
  fixes a_8 :: "addr"
  fixes a_7 :: "addr"
  shows "let a_10 :: addr = shift a_2 (0 :: int); a_11 :: addr = shift a_5 (0 :: int); a_12 :: addr = shift a_11 (1 :: int) in a_10 = shift a (0 :: int) \<longrightarrow> a_11 = a_10 \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_4 \<longrightarrow> p_valid_file t t_1 a_10 \<longrightarrow> \<not>invalid t a_12 (1 :: int) \<longrightarrow> i = -(1 :: int) \<or> i = (0 :: int) \<longrightarrow> a_12 = shift a_9 (7 :: int) \<or> a_12 = shift a_6 (8 :: int) \<or> a_12 = shift a_10 (1 :: int) \<or> shift (shift a_8 (0 :: int)) (1 :: int) = a_12 \<or> shift a_10 (2 :: int) = a_12 \<or> shift (shift a_7 (0 :: int)) (2 :: int) = a_12"
  sorry
end
