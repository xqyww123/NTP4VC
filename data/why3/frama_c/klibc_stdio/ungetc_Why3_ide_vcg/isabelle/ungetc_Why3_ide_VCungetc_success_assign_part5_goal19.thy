theory ungetc_Why3_ide_VCungetc_success_assign_part5_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal19:
  fixes a_10 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes a_8 :: "addr"
  fixes a_9 :: "addr"
  fixes a_7 :: "addr"
  shows "let a_11 :: addr = shift a_10 (7 :: int) in shift a_2 (0 :: int) = shift a (0 :: int) \<longrightarrow> t_1 (shift a_4 (8 :: int)) = (0 :: int) \<longrightarrow> t_1 (shift a_10 (8 :: int)) = (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i \<longrightarrow> i \<le> (127 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_1 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_3 \<longrightarrow> \<not>invalid t a_11 (1 :: int) \<longrightarrow> \<not>addr_le (t_3 (shift a_5 (6 :: int))) (t_3 (shift a_6 (5 :: int))) \<longrightarrow> \<not>addr_le (t_3 (shift a_10 (6 :: int))) (t_3 (shift a_10 (5 :: int))) \<longrightarrow> a_11 = shift a_8 (6 :: int) \<or> a_11 = shift a_9 (7 :: int) \<or> shift (t_3 (shift a_7 (6 :: int))) (-(1 :: int)) = a_11"
  sorry
end
