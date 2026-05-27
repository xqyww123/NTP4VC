theory stack_empty_wd_Why3_ide_VCstack_empty_wd_post_equal_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_empty_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_empty_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "\<not>i = (1 :: int) \<longleftrightarrow> i = (0 :: int)"
  assumes fact1: "\<not>i_1 = (1 :: int) \<longleftrightarrow> i_1 = (0 :: int)"
  assumes fact2: "p_empty t_1 a \<longleftrightarrow> i_1 = (1 :: int)"
  assumes fact3: "p_empty t_1 a_1 \<longleftrightarrow> i = (1 :: int)"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "region (base a_1) \<le> (0 :: int)"
  assumes fact6: "framed t_2"
  assumes fact7: "linked t"
  assumes fact8: "is_sint32 i"
  assumes fact9: "is_sint32 i_1"
  assumes fact10: "valid_rw t a (3 :: int)"
  assumes fact11: "valid_rw t a_1 (3 :: int)"
  assumes fact12: "p_invariant t t_2 t_1 a"
  assumes fact13: "p_invariant t t_2 t_1 a_1"
  assumes fact14: "p_equal t_2 t_1 t_2 t_1 a_1 a"
  shows "i_1 = i"
  sorry
end
