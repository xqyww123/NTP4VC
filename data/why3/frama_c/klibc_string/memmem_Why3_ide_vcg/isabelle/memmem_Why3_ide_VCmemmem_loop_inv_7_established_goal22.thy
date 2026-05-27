theory memmem_Why3_ide_VCmemmem_loop_inv_7_established_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal22:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  shows "let x :: int = base a_1; a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr = shift a_2 (0 :: int) in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_4 i \<longrightarrow> separated a_4 i a_3 (1 :: int) \<longrightarrow> x = base a"
  sorry
end
