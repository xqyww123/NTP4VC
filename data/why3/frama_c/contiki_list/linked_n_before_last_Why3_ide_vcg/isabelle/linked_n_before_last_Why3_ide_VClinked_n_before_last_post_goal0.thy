theory linked_n_before_last_Why3_ide_VClinked_n_before_last_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = i_1 + i_2; a_3 :: addr = t_1 (shift a_2 (i + i_1 - (1 :: int))) in (0 :: int) < i \<longrightarrow> i_2 \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) (2147483646 :: int) \<longrightarrow> p_linked_n t t_1 a a_2 i_1 i a_1 \<longrightarrow> p_linked_n t t_1 (t_1 (shift a_2 x_1)) a_2 x_1 (i - (1 :: int) - i_2) a_3 \<longrightarrow> p_linked_n t t_1 a a_2 i_1 x a_3"
  sorry
end
