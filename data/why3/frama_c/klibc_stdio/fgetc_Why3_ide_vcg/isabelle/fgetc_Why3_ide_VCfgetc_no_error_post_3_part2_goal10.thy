theory fgetc_Why3_ide_VCfgetc_no_error_post_3_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal10:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_5 :: "addr"
  fixes a :: "addr"
  fixes a_6 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let a_7 :: addr = shift a_2 (0 :: int); x :: int = t_1 (shift a_4 (7 :: int)); x_1 :: int = t_2 (t_3 (shift a_5 (6 :: int))) in \<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> a_7 = shift a (0 :: int) \<longrightarrow> t_1 (shift a_6 (7 :: int)) = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> x_1 = -(1 :: int)"
  sorry
end
