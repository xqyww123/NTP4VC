theory X__fflush_Why3_ide_VC__fflush_loop_inv_5_established_part2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal9:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a (9 :: int)); a_1 :: addr = t_2 (shift a (5 :: int)) in t_1 (shift a (7 :: int)) = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 (t_1 (shift a (8 :: int))) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a \<longrightarrow> addr_le a_1 (shift a_1 ((32 :: int) + x))"
  sorry
end
