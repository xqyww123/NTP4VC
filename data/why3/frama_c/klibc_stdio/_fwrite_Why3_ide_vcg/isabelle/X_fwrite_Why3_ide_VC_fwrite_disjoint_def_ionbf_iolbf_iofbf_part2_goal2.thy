theory X_fwrite_Why3_ide_VC_fwrite_disjoint_def_ionbf_iolbf_iofbf_part2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_6 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 (shift a_4 (10 :: int)); x_1 :: int = t_1 (shift a_5 (10 :: int)) in shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> valid_rw t (shift a_6 (0 :: int)) i \<longrightarrow> \<not>x = (0 :: int) \<or> \<not>x_1 = (2 :: int)"
  sorry
end
