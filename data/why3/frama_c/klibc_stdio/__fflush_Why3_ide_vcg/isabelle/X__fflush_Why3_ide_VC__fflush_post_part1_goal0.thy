theory X__fflush_Why3_ide_VC__fflush_post_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  shows "let x :: int = t_1 (shift a_2 (7 :: int)) in shift a_2 (0 :: int) = shift a_1 (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_2 \<longrightarrow> i = -(1 :: int) \<or> i = (0 :: int) \<longrightarrow> -(1 :: int) \<le> i"
  sorry
end
