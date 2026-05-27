theory zalloc_Why3_ide_VCzalloc_nonzero_post_part1_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Compound_Compound"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_1 i \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> havoc t_1 t_2 a_1 i (shift a i_1) = (0 :: int)) \<longrightarrow> valid_rw t a_1 ((1 :: int) + i)"
  sorry
end
