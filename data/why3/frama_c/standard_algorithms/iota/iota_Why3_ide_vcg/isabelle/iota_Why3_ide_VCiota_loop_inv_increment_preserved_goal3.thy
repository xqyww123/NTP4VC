theory iota_Why3_ide_VCiota_loop_inv_increment_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_iota_lib.Compound_Compound" "frama_c_standard_algorithms_iota_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_2; x_1 :: int = i - i_2; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1 in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> i + i_1 \<le> (2147483647 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_iota a_3 a i_2 x_1 \<longrightarrow> p_iota (a_3(a_2 := i)) a x x_1"
  sorry
end
