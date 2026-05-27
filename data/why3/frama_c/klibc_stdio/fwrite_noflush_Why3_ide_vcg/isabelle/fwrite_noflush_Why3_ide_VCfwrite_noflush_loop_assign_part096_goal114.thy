theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_assign_part096_goal114
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal114:
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  shows "let x :: int = base a_3; x_1 :: int = t_1 (shift a_1 (9 :: int)); x_2 :: int = to_uint32 (x_1 - i); a_4 :: addr = shift (shift a_1 (0 :: int)) (1 :: int); a_5 :: addr = shift a (0 :: int); a_6 :: addr = t_4 (shift a_1 (5 :: int)); a_7 :: addr = shift a_6 i; a_8 :: addr \<Rightarrow> int = havoc t_2 t_3 a_7 x_2; a_9 :: addr = shift a_2 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> t_1 (shift a_1 (7 :: int)) = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_4 \<le> i_5 \<longrightarrow> i < x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_2 \<le> i_4 \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> addr_le a_3 a \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_4 t_1 a_1 \<longrightarrow> addr_le a (shift a_3 i_5) \<longrightarrow> valid_rw t (shift a_3 (0 :: int)) i_5 \<longrightarrow> \<not>invalid t a_4 (1 :: int) \<longrightarrow> valid_rw t a_5 x_2 \<longrightarrow> valid_rw t a_7 x_2 \<longrightarrow> separated a_5 x_2 a_7 x_2 \<longrightarrow> (i_1 = -(1 :: int) \<longrightarrow> i_3 = (4 :: int) \<or> i_3 = (11 :: int)) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < x_2 \<longrightarrow> a_8 (shift a_6 (i_6 + i)) = a_8 (shift a i_6)) \<longrightarrow> a_4 = shift a_2 (8 :: int) \<or> shift a_9 (1 :: int) = a_4 \<or> shift a_9 (2 :: int) = a_4"
  sorry
end
