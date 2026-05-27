theory ftell_Why3_ide_VCftell_post_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal0:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_6 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let a_7 :: addr = shift a_2 (0 :: int); x :: int = t_1 (shift (shift a_6 (0 :: int)) (0 :: int)); x_1 :: int = t_1 (shift a_6 (8 :: int)); x_2 :: int = to_sint32 x_1; x_3 :: int = t_1 (shift a_6 (7 :: int)); x_4 :: int = to_sint32 x_3; x_5 :: int = t_1 (shift a_4 (7 :: int)); x_6 :: int = t_1 (shift a_5 (8 :: int)) in a_7 = shift a (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x_2 \<le> i + x_4 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint64 i \<longrightarrow> is_uint32 x_5 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_uint32 x_6 \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_file t t_1 a_7 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint64 (i + x_4 - x_2) \<longrightarrow> i = -(1 :: int) \<or> i \<le> (0 :: int) \<or> to_sint32 x_6 \<le> i + to_sint32 x_5"
  sorry
end
