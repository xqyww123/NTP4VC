theory iota_Why3_ide_VCiota_assert_rte_signed_overflow_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_iota_lib.Compound_Compound" "frama_c_standard_algorithms_iota_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = i + i_2; a_1 :: addr = shift a (0 :: int) in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i + i_1 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> p_iota (havoc t_1 t_2 a_1 i_1) a i_2 i \<longrightarrow> x \<le> (2147483646 :: int)"
  sorry
end
