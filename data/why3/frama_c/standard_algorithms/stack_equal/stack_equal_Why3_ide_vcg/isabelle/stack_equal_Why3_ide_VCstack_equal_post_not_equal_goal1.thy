theory stack_equal_Why3_ide_VCstack_equal_post_not_equal_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_equal_lib.Compound_Compound" "frama_c_standard_algorithms_stack_equal_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes p :: "bool"
  shows "let a_2 :: addr = shift a (2 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a_1 (2 :: int); x_1 :: int = t_1 a_3; a_4 :: addr = shift a_1 (0 :: int); a_5 :: addr = t_2 a_4; a_6 :: addr = shift a (0 :: int); a_7 :: addr = t_2 a_6 in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> (if x_1 = x then p = False \<and> (p_equalranges_1' t_1 t_1 a_5 x_1 a_7 \<longleftrightarrow> \<not>i_1 = (0 :: int)) \<and> valid_rd t a_6 (1 :: int) \<and> valid_rd t a_4 (1 :: int) \<and> valid_rd t (shift a_7 (0 :: int)) x_1 \<and> valid_rd t (shift a_5 (0 :: int)) x_1 \<and> (if i_1 = (0 :: int) then i = (0 :: int) else i = (1 :: int)) else i = (0 :: int)) \<longrightarrow> \<not>p_equal t_2 t_1 t_2 t_1 a_1 a \<longleftrightarrow> i = (0 :: int)"
  sorry
end
