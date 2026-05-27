theory list_init_Why3_ide_VClist_init_post_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_contiki_list_lib.Compound_Compound" "frama_c_contiki_list_lib.S1_list_S1_list" "frama_c_contiki_list_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (2147483646 :: int) \<longrightarrow> separated a (1 :: int) a_2 (2147483646 :: int) \<longrightarrow> separated (t_1 a) (4 :: int) a_2 (2147483646 :: int) \<longrightarrow> p_linked_n t (t_1(a := Mk_addr (0 :: int) (0 :: int))) (Mk_addr (0 :: int) (0 :: int)) a_1 (0 :: int) (0 :: int) (Mk_addr (0 :: int) (0 :: int))"
  sorry
end
