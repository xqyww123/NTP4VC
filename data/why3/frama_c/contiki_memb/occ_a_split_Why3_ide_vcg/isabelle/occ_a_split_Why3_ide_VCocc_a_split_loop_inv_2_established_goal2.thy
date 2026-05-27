theory occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  assumes fact0: "i_3 \<le> i"
  assumes fact1: "i_1 \<le> i_3"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "sconst t"
  assumes fact4: "is_sint32 i"
  assumes fact5: "is_sint32 i_1"
  assumes fact6: "is_sint32 i_2"
  assumes fact7: "is_sint32 i_3"
  shows "l_occ_a t i_2 a i_3 i_3 = (0 :: int)"
  sorry
end
