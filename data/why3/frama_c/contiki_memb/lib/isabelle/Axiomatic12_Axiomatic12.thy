theory Axiomatic12_Axiomatic12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_empty_block :: "(int \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_empty_block malloc_0 s \<longleftrightarrow> malloc_0 (base s) = (0 :: int) \<and> base_offset (offset s) = (0 :: int)" for malloc_0 s
definition p_valid_or_empty :: "(int \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_valid_or_empty malloc_0 s n \<longleftrightarrow> valid_rw malloc_0 (shift s (0 :: int)) n \<and> (p_empty_block malloc_0 s \<or> valid_rd malloc_0 s (1 :: int))" for malloc_0 s n
end
