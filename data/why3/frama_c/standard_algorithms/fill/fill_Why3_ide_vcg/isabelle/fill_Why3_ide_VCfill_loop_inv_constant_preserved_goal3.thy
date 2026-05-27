theory fill_Why3_ide_VCfill_loop_inv_constant_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_fill_lib.Compound_Compound" "frama_c_standard_algorithms_fill_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = (1 :: int) + i_2; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1 in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_constantrange a_3 a (0 :: int) i_2 i \<longrightarrow> p_constantrange (a_3(a_2 := i)) a (0 :: int) x i"
  sorry
end
