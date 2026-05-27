theory replace_Why3_ide_VCreplace_loop_inv_unchanged_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_replace_lib.Compound_Compound" "frama_c_standard_algorithms_replace_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_3; a_1 :: addr = shift a i_3; a_2 :: addr = shift a (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i_2; a_4 :: int = a_3 a_1 in i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 i_2 \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_unchanged_1' a_3 t_2 a i_3 i_2 \<longrightarrow> p_replace_2' a_3 t_2 a i_3 i_1 i \<longrightarrow> (if a_4 = i_1 then a_3(a_1 := i) = t_3 \<and> valid_rw t a_1 (1 :: int) else a_3 = t_3) \<longrightarrow> p_unchanged_1' t_3 t_2 a x i_2"
  sorry
end
