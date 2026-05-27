theory fwrite_noflush_Why3_ide_VCfwrite_noflush_loop_inv_5_preserved_part51_goal51
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal51:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_1 (shift a_1 (9 :: int)); a_3 :: addr = shift a (0 :: int); a_4 :: addr = t_4 (shift a_1 (5 :: int)); a_5 :: addr = shift a_4 (0 :: int); a_6 :: addr \<Rightarrow> int = havoc t_2 t_3 a_5 i_3 in \<not>i_3 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> t_1 (shift a_1 (7 :: int)) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> i_3 < x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_2 \<longrightarrow> addr_le a_2 a \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_4 t_1 a_1 \<longrightarrow> addr_le a (shift a_2 i_4) \<longrightarrow> valid_rw t a_3 i_3 \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_4 \<longrightarrow> valid_rw t a_5 i_3 \<longrightarrow> separated a_3 i_3 a_5 i_3 \<longrightarrow> (i = -(1 :: int) \<longrightarrow> i_2 = (4 :: int) \<or> i_2 = (11 :: int)) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_3 \<longrightarrow> a_6 (shift a_4 i_5) = a_6 (shift a i_5)) \<longrightarrow> addr_le a_2 (shift a i_3)"
  sorry
end
