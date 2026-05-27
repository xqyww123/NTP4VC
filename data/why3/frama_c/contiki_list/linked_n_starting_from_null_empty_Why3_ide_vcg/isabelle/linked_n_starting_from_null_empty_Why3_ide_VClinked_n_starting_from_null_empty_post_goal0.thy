theory linked_n_starting_from_null_empty_Why3_ide_VClinked_n_starting_from_null_empty_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Axiomatic_Axiomatic" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "framed t_1"
  assumes fact2: "linked t"
  assumes fact3: "is_sint32 i"
  assumes fact4: "is_sint32 i_1"
  assumes fact5: "p_linked_n t t_1 (Mk_addr (0 :: int) (0 :: int)) a i_1 i (Mk_addr (0 :: int) (0 :: int))"
  shows "i = (0 :: int)"
  sorry
end
