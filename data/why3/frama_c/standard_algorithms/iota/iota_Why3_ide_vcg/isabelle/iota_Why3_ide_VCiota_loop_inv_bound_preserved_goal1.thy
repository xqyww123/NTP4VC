theory iota_Why3_ide_VCiota_loop_inv_bound_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_iota_lib.Compound_Compound" "frama_c_standard_algorithms_iota_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = i_1 + i_2; x_2 :: int = i - i_1; a_1 :: addr = shift a (0 :: int) in i_1 \<le> i \<longrightarrow> i < x \<longrightarrow> i \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> x \<le> (2147483647 :: int) \<longrightarrow> i \<le> (4294967294 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> is_uint32 ((1 :: int) + i - i_1) \<longrightarrow> valid_rw t (shift a x_2) (1 :: int) \<longrightarrow> p_iota (havoc t_1 t_2 a_1 i_2) a x_2 i_1 \<longrightarrow> i_1 \<le> (1 :: int) + i"
  sorry
end
