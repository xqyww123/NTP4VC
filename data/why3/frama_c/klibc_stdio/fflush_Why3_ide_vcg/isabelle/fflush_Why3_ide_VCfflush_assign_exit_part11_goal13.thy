theory fflush_Why3_ide_VCfflush_assign_exit_part11_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Globals_Globals" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal13:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_6 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_5 :: "addr"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = t_1 (shift a_6 (8 :: int)); a_7 :: addr = shift (shift a_6 (0 :: int)) (1 :: int) in \<not>Mk_addr (1723 :: int) (0 :: int) = a_6 \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> region (0 :: int) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_2 t_1 a_6 \<longrightarrow> \<not>invalid t a_7 (1 :: int) \<longrightarrow> a_7 = shift a_5 (7 :: int) \<or> a_7 = shift a_2 (8 :: int) \<or> a_7 = shift (shift a_4 (0 :: int)) (1 :: int) \<or> shift (shift a_3 (0 :: int)) (2 :: int) = a_7"
  sorry
end
