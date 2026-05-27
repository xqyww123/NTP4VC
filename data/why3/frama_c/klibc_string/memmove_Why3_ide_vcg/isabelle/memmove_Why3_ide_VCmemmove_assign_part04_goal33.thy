theory memmove_Why3_ide_VCmemmove_assign_part04_goal33
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal33:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int) in (0 :: int) \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> addr_lt a_1 a \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> \<not>invalid t a_2 (i - i_1) \<longrightarrow> (0 :: int) \<le> i_1"
  sorry
end
