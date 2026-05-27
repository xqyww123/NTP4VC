theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_assign_part070_goal103
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal103:
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = base a_3; x_1 :: int = t_1 (shift a_2 (9 :: int)); a_4 :: addr = shift a_2 (0 :: int); x_2 :: int = t_1 (shift a_4 (0 :: int)); a_5 :: addr = shift a_4 (2 :: int); a_6 :: addr = shift a_1 (0 :: int) in \<not>i_2 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> t_1 (shift a_2 (7 :: int)) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> x_1 \<le> i_2 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> -(1 :: int) \<le> i_2 \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_3 a \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_2 \<longrightarrow> addr_le a (shift a_3 i_3) \<longrightarrow> valid_rw t (shift a (0 :: int)) i_2 \<longrightarrow> valid_rw t (shift a_3 (0 :: int)) i_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> \<not>invalid t a_5 (1 :: int) \<longrightarrow> a_5 = shift a_1 (8 :: int) \<or> a_5 = shift a_6 (1 :: int) \<or> a_5 = shift a_6 (2 :: int)"
  sorry
end
