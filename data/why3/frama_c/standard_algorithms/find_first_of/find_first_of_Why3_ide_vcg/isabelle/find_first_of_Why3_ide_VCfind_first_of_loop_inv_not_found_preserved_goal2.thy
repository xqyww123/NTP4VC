theory find_first_of_Why3_ide_VCfind_first_of_loop_inv_not_found_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_first_of_lib.Compound_Compound" "frama_c_standard_algorithms_find_first_of_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_2; a_2 :: addr = shift a_1 i_2; x_1 :: int = t_1 a_2 in (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x \<longrightarrow> is_sint32 (t_1 (shift a i)) \<longrightarrow> is_sint32 x_1 \<longrightarrow> \<not>p_hasvalueof t_1 a_1 i_2 a i \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> \<not>p_hasvalue_1' t_1 a (0 :: int) i x_1 \<longrightarrow> \<not>p_hasvalueof t_1 a_1 x a i"
  sorry
end
