theory memmove_Why3_ide_VCmemmove_loop_inv_16_established_part2_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal22:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> \<not>addr_lt a_1 a \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> addr_le a_2 a_2"
  sorry
end
