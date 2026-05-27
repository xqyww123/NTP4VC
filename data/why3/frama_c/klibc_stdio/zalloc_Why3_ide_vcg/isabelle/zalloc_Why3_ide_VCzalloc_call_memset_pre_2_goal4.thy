theory zalloc_Why3_ide_VCzalloc_call_memset_pre_2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Compound_Compound"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rw t a_1 i) \<longrightarrow> valid_rw t a_1 i"
  sorry
end
