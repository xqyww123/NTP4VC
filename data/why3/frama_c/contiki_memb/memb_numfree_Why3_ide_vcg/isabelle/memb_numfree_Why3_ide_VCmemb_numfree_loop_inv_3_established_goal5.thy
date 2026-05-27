theory memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "framed t_3"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_2"
  assumes fact4: "is_uint16 (t_1 (shift a (1 :: int)))"
  assumes fact5: "p_valid_memb t t_3 t_1 a"
  shows "l_occ_a t_2 (0 :: int) (t_3 (shift a (2 :: int))) (0 :: int) (0 :: int) = (0 :: int)"
  sorry
end
