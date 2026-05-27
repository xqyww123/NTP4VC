theory X_fwrite_Why3_ide_VC_fwrite_call_fwrite_noflush_pre_3_part1_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal13:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_5 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 (shift a_4 (10 :: int)) in \<not>i = (0 :: int) \<longrightarrow> shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> \<not>x = (1 :: int) \<longrightarrow> \<not>x = (2 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> valid_rw t (shift a_5 (0 :: int)) i \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_4"
  sorry
end
