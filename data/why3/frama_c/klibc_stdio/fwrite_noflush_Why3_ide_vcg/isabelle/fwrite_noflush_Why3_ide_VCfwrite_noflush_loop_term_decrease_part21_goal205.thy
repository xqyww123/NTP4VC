theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_term_decrease_part21_goal205
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal205:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_7 :: "int"
  fixes i_5 :: "int"
  fixes i_8 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_1 (shift a_1 (9 :: int)); x_2 :: int = to_uint32 (x_1 - i_3); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr = shift a (0 :: int); a_5 :: addr = t_4 (shift a_1 (5 :: int)); a_6 :: addr = shift a_5 i_3; a_7 :: addr \<Rightarrow> int = havoc t_2 t_3 a_6 x_2 in \<not>i_3 = (0 :: int) \<longrightarrow> \<not>i_7 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> t_1 (shift a_1 (7 :: int)) = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> i_5 \<le> i_7 \<longrightarrow> (0 :: int) \<le> i_8 \<longrightarrow> i_7 \<le> i_8 \<longrightarrow> x_1 \<le> i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_2 \<le> i_7 \<longrightarrow> -(1 :: int) \<le> i_4 \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_uint32 i_8 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_sint32 i_6 \<longrightarrow> addr_le a_2 a \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_4 t_1 a_1 \<longrightarrow> addr_le a (shift a_2 i_8) \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_8 \<longrightarrow> p_valid_io_file_pvt t t_4 (t_1(shift a_3 (2 :: int) := i_2, shift a_3 (1 :: int) := i_1, shift a_1 (8 :: int) := i)) a_1 \<longrightarrow> valid_rw t a_4 x_2 \<longrightarrow> valid_rw t a_6 x_2 \<longrightarrow> separated a_4 x_2 a_6 x_2 \<longrightarrow> (i_4 = -(1 :: int) \<longrightarrow> i_6 = (4 :: int) \<or> i_6 = (11 :: int)) \<longrightarrow> (\<forall>(i_9 :: int). (0 :: int) \<le> i_9 \<longrightarrow> i_9 < x_2 \<longrightarrow> a_7 (shift a_5 (i_9 + i_3)) = a_7 (shift a i_9)) \<longrightarrow> to_uint32 (i_7 - x_2) < i_7"
  sorry
end
