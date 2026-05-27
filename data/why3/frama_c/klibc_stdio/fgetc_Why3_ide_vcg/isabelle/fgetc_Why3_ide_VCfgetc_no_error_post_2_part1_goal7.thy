theory fgetc_Why3_ide_VCfgetc_no_error_post_2_part1_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal7:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_7 :: "addr"
  fixes a_4 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_6 :: "addr"
  fixes a_5 :: "addr"
  shows "let a_8 :: addr = shift a_2 (0 :: int); x :: int = t_1 (shift a_7 (7 :: int)); x_1 :: int = t_1 (shift a_4 (7 :: int)); a_9 :: addr = shift a_7 (6 :: int); a_10 :: addr = t_3 a_9; x_2 :: int = t_2 a_10 in \<not>a_8 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> a_8 = shift a (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint32 x_2 \<longrightarrow> (t_3(a_9 := shift a_10 (1 :: int))) (shift a_6 (6 :: int)) = shift (t_3 (shift a_5 (6 :: int))) (1 :: int)"
  sorry
end
