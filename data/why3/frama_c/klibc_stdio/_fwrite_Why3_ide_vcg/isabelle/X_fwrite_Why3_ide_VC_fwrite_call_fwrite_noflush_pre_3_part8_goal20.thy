theory X_fwrite_Why3_ide_VC_fwrite_call_fwrite_noflush_pre_3_part8_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal20:
  fixes i_7 :: "int"
  fixes i_8 :: "int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  shows "let x :: int = i_7 + i_8; a_6 :: addr = shift a_4 (0 :: int); a_7 :: addr = shift a_5 (8 :: int); a_8 :: addr = shift a_5 (0 :: int); a_9 :: addr = shift a_8 (1 :: int); a_10 :: addr = shift a_8 (2 :: int); m :: addr \<Rightarrow> int = t_1(a_10 := i_2, a_9 := i_1, a_7 := i) in \<not>i_7 = (0 :: int) \<longrightarrow> \<not>i_8 = (0 :: int) \<longrightarrow> shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> t_1 (shift a_5 (10 :: int)) = (1 :: int) \<longrightarrow> t_2 (shift a_4 (to_uint32 (i_8 - (1 :: int)))) = (10 :: int) \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> (0 :: int) \<le> i_8 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_7 \<longrightarrow> is_uint32 i_8 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_5 \<longrightarrow> valid_rw t a_6 i_8 \<longrightarrow> valid_rw t a_6 x \<longrightarrow> p_valid_io_file_pvt t t_3 m a_5 \<longrightarrow> (\<forall>(i_9 :: int). i_8 < i_9 \<longrightarrow> i_9 \<le> x \<longrightarrow> \<not>t_2 (shift a_4 (i_9 - (1 :: int))) = (10 :: int)) \<longrightarrow> p_valid_io_file_pvt t t_3 (m(shift a_5 (7 :: int) := i_6, a_9 := i_5, a_10 := i_4, a_7 := i_3)) a_5"
  sorry
end
