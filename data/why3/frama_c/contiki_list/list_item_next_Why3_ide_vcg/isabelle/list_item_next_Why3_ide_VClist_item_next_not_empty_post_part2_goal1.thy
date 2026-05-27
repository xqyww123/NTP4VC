theory list_item_next_Why3_ide_VClist_item_next_not_empty_post_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "\<not>Mk_addr (0 :: int) (0 :: int) = a"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "framed t_1"
  assumes fact4: "linked t"
  assumes fact5: "is_sint32 i"
  assumes fact6: "is_sint32 i_1"
  assumes fact7: "p_linked_n t t_1 a a_1 i_1 i (Mk_addr (0 :: int) (0 :: int))"
  shows "p_linked_n t t_1 (t_1 (shift a (0 :: int))) a_1 ((1 :: int) + i_1) (i - (1 :: int)) (Mk_addr (0 :: int) (0 :: int))"
  sorry
end
