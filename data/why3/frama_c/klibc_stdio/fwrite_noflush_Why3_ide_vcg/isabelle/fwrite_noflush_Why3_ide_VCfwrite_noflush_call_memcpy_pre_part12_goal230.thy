theory fwrite_noflush_Why3_ide_VCfwrite_noflush_call_memcpy_pre_part12_goal230
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal230:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_1 (shift a_1 (9 :: int)); x_2 :: int = to_uint32 (x_1 - i) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> t_1 (shift a_1 (7 :: int)) = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_4 \<le> i_5 \<longrightarrow> i < x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_2 \<le> i_4 \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> addr_le a_2 a \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> addr_le a (shift a_2 i_5) \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_5 \<longrightarrow> (i_1 = -(1 :: int) \<longrightarrow> i_3 = (4 :: int) \<or> i_3 = (11 :: int)) \<longrightarrow> separated (shift a (0 :: int)) x_2 (shift (t_3 (shift a_1 (5 :: int))) i) x_2"
  sorry
end
