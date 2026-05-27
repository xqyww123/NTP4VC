theory memmem_Why3_ide_VCmemmem_loop_inv_9_established_part1_goal26
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal26:
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let a_4 :: addr = shift a_2 (0 :: int); a_5 :: addr = shift a_3 (0 :: int) in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_5 i a_4 (1 :: int) \<longrightarrow> addr_le a_1 a"
  sorry
end
