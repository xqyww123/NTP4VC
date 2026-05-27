theory fwrite_noflush_Why3_ide_VCfwrite_noflush_post_part9_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal8:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = base a_2 in x = base a \<longrightarrow> i_1 \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_3 \<longrightarrow> addr_le a_2 a \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> addr_le a (shift a_2 i_4) \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_4 \<longrightarrow> (i = -(1 :: int) \<longrightarrow> i_3 = (4 :: int) \<or> i_3 = (11 :: int)) \<longrightarrow> (0 :: int) \<le> i_2"
  sorry
end
