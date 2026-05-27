theory X__fflush_Why3_ide_VC__fflush_loop_assign_part02_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal12:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = t_2 (shift a_2 (5 :: int)); x :: int = base a_3; x_1 :: int = base a; x_2 :: int = base (t_2 (shift a_2 (6 :: int))); x_3 :: int = t_1 (shift (shift a_2 (0 :: int)) (0 :: int)); x_4 :: int = t_1 (shift a_2 (9 :: int)); a_4 :: addr = shift a_2 (8 :: int); a_5 :: addr = shift a_1 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> t_1 (shift a_2 (7 :: int)) = (0 :: int) \<longrightarrow> x = x_1 \<longrightarrow> x_2 = x_1 \<longrightarrow> x_2 = x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x_4 \<longrightarrow> is_uint32 (t_1 a_4) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_2 \<longrightarrow> \<not>invalid t a_4 (1 :: int) \<longrightarrow> addr_le a_3 a \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> is_sint32 x_3 \<longrightarrow> addr_le a (shift a_3 ((32 :: int) + x_4)) \<longrightarrow> a_4 = shift a_1 (8 :: int) \<or> shift a_5 (1 :: int) = a_4 \<or> shift a_5 (2 :: int) = a_4"
  sorry
end
