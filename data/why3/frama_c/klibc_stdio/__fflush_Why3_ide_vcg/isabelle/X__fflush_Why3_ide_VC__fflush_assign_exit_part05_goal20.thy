theory X__fflush_Why3_ide_VC__fflush_assign_exit_part05_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal20:
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  shows "let a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr = shift a_3 (7 :: int); x :: int = t_1 a_5; a_6 :: addr = shift (shift a (0 :: int)) (1 :: int) in a_4 = shift a_2 (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> \<not>invalid t a_6 (1 :: int) \<longrightarrow> a_6 = a_5 \<or> a_6 = shift a_3 (8 :: int) \<or> shift a_4 (1 :: int) = a_6 \<or> shift a_4 (2 :: int) = a_6"
  sorry
end
