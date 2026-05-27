theory fseek_Why3_ide_VCfseek_call___fflush_pre_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal20:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 (shift a_4 (8 :: int)) in shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint64 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> i_1 = (0 :: int) \<or> i_1 = (1 :: int) \<or> i_1 = (2 :: int) \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_4"
  sorry
end
