theory fseek_Why3_ide_VCfseek_call_lseek_pre_part4_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal24:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 (shift (shift a_4 (0 :: int)) (0 :: int)) in \<not>i_1 = (1 :: int) \<longrightarrow> shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> t_1 (shift a_4 (8 :: int)) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint64 i \<longrightarrow> is_uint32 (t_1 (shift a_4 (7 :: int))) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> is_sint32 x \<longrightarrow> i_1 = (0 :: int) \<or> i_1 = (2 :: int) \<longrightarrow> (0 :: int) \<le> x"
  sorry
end
