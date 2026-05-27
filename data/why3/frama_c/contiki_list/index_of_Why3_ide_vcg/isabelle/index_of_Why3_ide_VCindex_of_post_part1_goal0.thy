theory index_of_Why3_ide_VCindex_of_post_part1_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.A_Index_of_item_A_Index_of_item"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "i \<le> i_1"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "region (base a_1) \<le> (0 :: int)"
  assumes fact5: "framed t_1"
  assumes fact6: "linked t"
  assumes fact7: "is_sint32 i"
  assumes fact8: "is_sint32 i_1"
  assumes fact9: "i_1 \<le> i \<longrightarrow> valid_rw t (shift a_1 i_1) (i - i_1)"
  shows "l_index_of t_1 a a_1 i_1 i = i"
  sorry
end
