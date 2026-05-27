theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_assign_part105_goal123
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal123:
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_7 :: "int"
  fixes i_3 :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  shows "let x :: int = base a_2; a_3 :: addr = shift a_1 (7 :: int); x_1 :: int = t_1 a_3; x_2 :: int = t_1 (shift a_1 (9 :: int)); a_4 :: addr = shift a_1 (0 :: int); x_3 :: int = t_1 (shift a_4 (0 :: int)) in \<not>i_6 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> i_4 \<le> i_6 \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> i_6 \<le> i_7 \<longrightarrow> x_2 \<le> i_6 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> -(1 :: int) \<le> i_3 \<longrightarrow> -(1 :: int) \<le> i_6 \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_sint32 i_5 \<longrightarrow> addr_le a_2 a \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> \<not>invalid t a_3 (1 :: int) \<longrightarrow> addr_le a (shift a_2 i_7) \<longrightarrow> valid_rw t (shift a (0 :: int)) i_6 \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_7 \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_valid_io_file_pvt t t_3 (t_1(shift a_4 (2 :: int) := i_2, shift a_4 (1 :: int) := i_1, shift a_1 (8 :: int) := i)) a_1 \<longrightarrow> \<not>(i_3 = -(1 :: int) \<longrightarrow> i_5 = (4 :: int) \<or> i_5 = (11 :: int))"
  sorry
end
