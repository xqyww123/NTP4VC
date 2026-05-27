theory memset_Why3_ide_VCmemset_assign_part3_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal6:
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in i < i_1 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> \<not>invalid t a_1 (i_1 - i) \<longrightarrow> (0 :: int) \<le> i"
  sorry
end
