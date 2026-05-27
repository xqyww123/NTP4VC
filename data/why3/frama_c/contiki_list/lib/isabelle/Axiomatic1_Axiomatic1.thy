theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "S1_list_S1_list"
begin
definition p_unchanged :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_unchanged malloc_0 mptr_0 mflt_0 malloc_1 mptr_1 mflt_1 array_0 down_0 up_0 \<longleftrightarrow> (\<forall>(i :: int). let a :: addr = shift array_0 i; a_1 :: addr = mptr_0 a; a_2 :: addr = mptr_1 a in down_0 \<le> i \<longrightarrow> i < up_0 \<longrightarrow> a_1 = a_2 \<and> eqs1_list (load_s1_list a_2 mflt_1 mptr_1) (load_s1_list a_1 mflt_0 mptr_0) \<and> (valid_rw malloc_1 a_2 (4 :: int) \<longrightarrow> valid_rw malloc_0 a_1 (4 :: int)))" for malloc_0 mptr_0 mflt_0 malloc_1 mptr_1 mflt_1 array_0 down_0 up_0
definition p_array_swipe_left :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_array_swipe_left mptr_0 mptr_1 array_0 down_0 up_0 \<longleftrightarrow> (\<forall>(i :: int). down_0 \<le> i \<longrightarrow> i < up_0 \<longrightarrow> mptr_1 (shift array_0 ((1 :: int) + i)) = mptr_0 (shift array_0 i))" for mptr_0 mptr_1 array_0 down_0 up_0
definition p_array_swipe_right :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_array_swipe_right mptr_0 mptr_1 array_0 down_0 up_0 \<longleftrightarrow> (\<forall>(i :: int). down_0 \<le> i \<longrightarrow> i < up_0 \<longrightarrow> mptr_1 (shift array_0 (i - (1 :: int))) = mptr_0 (shift array_0 i))" for mptr_0 mptr_1 array_0 down_0 up_0
end
