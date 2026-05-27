theory ftell_Why3_ide_VCftell_call_lseek_pre_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let a_5 :: addr = shift a_2 (0 :: int); x :: int = t_1 (shift (shift a_4 (0 :: int)) (0 :: int)) in a_5 = shift a (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 (t_1 (shift a_4 (7 :: int))) \<longrightarrow> is_uint32 (t_1 (shift a_4 (8 :: int))) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_file t t_1 a_5 \<longrightarrow> is_sint32 x \<longrightarrow> (0 :: int) \<le> x"
  sorry
end
