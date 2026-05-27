theory memcpy_Why3_ide_VCmemcpy_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i; a_3 :: addr = shift a_1 i; a_4 :: addr = shift a (0 :: int); a_5 :: addr = shift a_1 (0 :: int); a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_5 i in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> addr_le a_3 a_3 \<longrightarrow> valid_rw t a_4 i \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_4 i a_5 i \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> a_6 (shift a_1 i_2) = a_6 (shift a i_2)) \<longrightarrow> a_6 (shift a_1 i_1) = a_6 (shift a i_1)"
  sorry
end
