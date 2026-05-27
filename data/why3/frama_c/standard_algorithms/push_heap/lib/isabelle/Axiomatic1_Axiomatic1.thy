theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_Count_A_Count" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_multisetadd :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetadd mint_0 mint_1 a n val_0 \<longleftrightarrow> (1 :: int) + l_count_1' mint_1 a (0 :: int) n val_0 = l_count_1' mint_0 a (0 :: int) n val_0" for mint_0 mint_1 a n val_0
definition p_multisetminus :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetminus mint_0 mint_1 a n val_0 \<longleftrightarrow> (1 :: int) + l_count_1' mint_0 a (0 :: int) n val_0 = l_count_1' mint_1 a (0 :: int) n val_0" for mint_0 mint_1 a n val_0
definition p_multisetretain :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetretain mint_0 mint_1 a n v \<longleftrightarrow> l_count_1' mint_1 a (0 :: int) n v = l_count_1' mint_0 a (0 :: int) n v" for mint_0 mint_1 a n v
definition p_multisetretainrest_3' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetretainrest_3' mint_0 mint_1 a n v w \<longleftrightarrow> (\<forall>(i :: int). \<not>i = v \<longrightarrow> \<not>i = w \<longrightarrow> is_sint32 i \<longrightarrow> p_multisetretain mint_0 mint_1 a n i)" for mint_0 mint_1 a n v w
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
end
