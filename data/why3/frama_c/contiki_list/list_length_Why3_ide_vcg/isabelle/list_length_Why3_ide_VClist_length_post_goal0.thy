theory list_length_Why3_ide_VClist_length_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "framed t_1"
  assumes fact5: "linked t"
  assumes fact6: "is_sint32 i"
  assumes fact7: "is_sint32 i_1"
  assumes fact8: "is_sint32 i_2"
  assumes fact9: "valid_rw t a (1 :: int)"
  assumes fact10: "p_linked_n t t_1 (t_1 a) a_1 i_2 i (Mk_addr (0 :: int) (0 :: int))"
  assumes fact11: "p_linked_n t t_1 (Mk_addr (0 :: int) (0 :: int)) a_1 (i_1 + i_2) (i - i_1) (Mk_addr (0 :: int) (0 :: int))"
  shows "i_1 = i"
  sorry
end
