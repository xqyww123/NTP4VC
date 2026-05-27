theory occ_a_split_Why3_ide_VCocc_a_split_assert_rte_signed_overflow_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes t :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  assumes fact0: "l_occ_a t i_3 a i_2 i_4 + l_occ_a t i_3 a i_4 i_1 = l_occ_a t i_3 a i_2 i_1"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "i_4 \<le> i"
  assumes fact3: "i_1 < i"
  assumes fact4: "i_4 \<le> i_1"
  assumes fact5: "i_2 \<le> i_4"
  assumes fact6: "region (base a) \<le> (0 :: int)"
  assumes fact7: "sconst t"
  assumes fact8: "is_sint32 i"
  assumes fact9: "is_sint32 i_1"
  assumes fact10: "is_sint32 i_2"
  assumes fact11: "is_sint32 i_3"
  assumes fact12: "is_sint32 i_4"
  shows "i_1 \<le> (2147483646 :: int)"
  sorry
end
