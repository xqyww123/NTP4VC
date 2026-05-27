theory memswap_Why3_ide_VCmemswap_assign_part6_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal14:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = i_1 - i in (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> \<not>invalid t a_2 x \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> included a_2 x a_3 i_1 \<or> (i < i_1 \<longrightarrow> (0 :: int) \<le> i)"
  sorry
end
