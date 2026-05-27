theory fgets_Why3_ide_VCfgets_call_fgetc_pre_2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal9:
  fixes a_2 :: "addr"
  fixes a_5 :: "addr"
  fixes a :: "addr"
  fixes a_6 :: "addr"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  shows "let a_7 :: addr = shift a_2 (0 :: int); x :: int = base a_5 in \<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> a_7 = shift a (0 :: int) \<longrightarrow> base a_6 = x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_le a_6 a_5 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> addr_le a_5 (shift a_6 i_1) \<longrightarrow> p_valid_file t t_1 a_7 \<longrightarrow> shift a_4 (0 :: int) = a_7"
  sorry
end
