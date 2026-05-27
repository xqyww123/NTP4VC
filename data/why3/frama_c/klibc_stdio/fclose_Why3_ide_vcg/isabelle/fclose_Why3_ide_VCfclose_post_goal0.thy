theory fclose_Why3_ide_VCfclose_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i :: "int"
  fixes a_5 :: "addr"
  fixes i_1 :: "int"
  fixes a_6 :: "addr"
  fixes i_2 :: "int"
  fixes a_7 :: "addr"
  fixes i_3 :: "int"
  fixes a_10 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_8 :: "addr"
  fixes a_9 :: "addr"
  shows "let a_11 :: addr = shift a_2 (0 :: int); x :: int = (t_1(shift a_7 (7 :: int) := i_3, shift (shift a_6 (0 :: int)) (1 :: int) := i_2, shift (shift a_5 (0 :: int)) (2 :: int) := i_1, shift a_4 (8 :: int) := i)) (shift (shift a_10 (0 :: int)) (0 :: int)) in a_11 = shift a (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 (1 :: int) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_8 \<longrightarrow> is_sint32 x \<longrightarrow> (1 :: int) = -(1 :: int) \<or> (1 :: int) = (0 :: int) \<longrightarrow> a_11 = Mk_addr (0 :: int) (0 :: int) \<or> shift a_9 (0 :: int) = a_11 \<longrightarrow> (1 :: int) = (0 :: int) \<or> \<not>True"
  sorry
end
