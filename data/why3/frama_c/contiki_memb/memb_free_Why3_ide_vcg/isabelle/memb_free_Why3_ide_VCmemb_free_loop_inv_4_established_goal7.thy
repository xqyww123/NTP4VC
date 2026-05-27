theory memb_free_Why3_ide_VCmemb_free_loop_inv_4_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "framed t_3"
  assumes fact3: "linked t"
  assumes fact4: "sconst t_2"
  assumes fact5: "is_uint16 (t_1 (shift a_1 (1 :: int)))"
  assumes fact6: "p_valid_memb t t_3 t_1 a_1"
  assumes fact7: "valid_rd t (shift a_1 (3 :: int)) (1 :: int)"
  shows "l__memb_index t_3 t_1 a_1 (l__memb_ptr t_3 t_1 a_1 (0 :: int)) = (0 :: int)"
  sorry
end
