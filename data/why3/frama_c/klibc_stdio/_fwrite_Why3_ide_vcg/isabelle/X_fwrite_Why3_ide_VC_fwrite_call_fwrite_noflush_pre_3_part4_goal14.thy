theory X_fwrite_Why3_ide_VC_fwrite_call_fwrite_noflush_pre_3_part4_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal14:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = i + i_1 in \<not>i_1 = (0 :: int) \<longrightarrow> shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> t_1 (shift a_5 (10 :: int)) = (1 :: int) \<longrightarrow> t_2 (shift a_4 (to_uint32 (i_1 - (1 :: int)))) = (10 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> valid_rw t (shift a_4 (0 :: int)) x \<longrightarrow> (\<forall>(i_2 :: int). i_1 < i_2 \<longrightarrow> i_2 \<le> x \<longrightarrow> \<not>t_2 (shift a_4 (i_2 - (1 :: int))) = (10 :: int)) \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_5"
  sorry
end
