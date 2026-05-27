theory fseek_Why3_ide_VCfseek_assign_normal_part02_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal4:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_8 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_7 :: "addr"
  fixes a_4 :: "addr"
  fixes a_6 :: "addr"
  fixes a_5 :: "addr"
  shows "let a_9 :: addr = shift a_2 (0 :: int); x :: int = t_1 (shift a_8 (8 :: int)); a_10 :: addr = shift a_8 (7 :: int) in a_9 = shift a (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_2 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint64 i \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_3 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_8 \<longrightarrow> \<not>invalid t a_10 (1 :: int) \<longrightarrow> is_sint32 (t_1 (shift (shift a_8 (0 :: int)) (0 :: int))) \<longrightarrow> i_1 = (0 :: int) \<or> i_1 = (1 :: int) \<or> i_1 = (2 :: int) \<longrightarrow> a_10 = shift a_7 (7 :: int) \<or> shift a_4 (8 :: int) = a_10 \<or> shift a_9 (1 :: int) = a_10 \<or> shift (shift a_6 (0 :: int)) (1 :: int) = a_10 \<or> shift a_9 (2 :: int) = a_10 \<or> shift (shift a_5 (0 :: int)) (2 :: int) = a_10"
  sorry
end
