theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "S1_list_S1_list"
begin
inductive p_linked_n :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> bool" where
   Q_linked_n_bound: "(0 :: int) \<le> index_0 \<Longrightarrow> index_0 \<le> (2147483646 :: int) \<Longrightarrow> p_linked_n malloc_0 mptr_0 bound_0 array_0 index_0 (0 :: int) bound_0" for index_0 :: "int" and malloc_0 :: "int \<Rightarrow> int" and mptr_0 :: "addr \<Rightarrow> addr" and bound_0 :: "addr" and array_0 :: "addr"
 | Q_linked_n_cons: "mptr_0 (shift array_0 index_0) = root_0 \<Longrightarrow> (0 :: int) < n \<Longrightarrow> (0 :: int) \<le> index_0 \<Longrightarrow> (0 :: int) \<le> index_0 + n \<Longrightarrow> index_0 + n \<le> (2147483646 :: int) \<Longrightarrow> valid_rw malloc_0 root_0 (4 :: int) \<Longrightarrow> p_linked_n malloc_0 mptr_0 (mptr_0 (shift root_0 (0 :: int))) array_0 ((1 :: int) + index_0) (n - (1 :: int)) bound_0 \<Longrightarrow> p_linked_n malloc_0 mptr_0 root_0 array_0 index_0 n bound_0" for index_0 :: "int" and n :: "int" and mptr_0 :: "addr \<Rightarrow> addr" and array_0 :: "addr" and root_0 :: "addr" and malloc_0 :: "int \<Rightarrow> int" and bound_0 :: "addr"
end
