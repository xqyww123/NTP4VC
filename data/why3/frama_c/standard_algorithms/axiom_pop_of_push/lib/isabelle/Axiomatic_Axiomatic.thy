theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint"
begin
definition l_storage :: "(addr \<Rightarrow> addr) \<Rightarrow> addr \<Rightarrow> addr"
  where "l_storage mptr_0 s = mptr_0 (shift s (0 :: int))" for mptr_0 s
definition l_size :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
  where "l_size mint_0 s = mint_0 (shift s (2 :: int))" for mint_0 s
definition p_equalranges_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_equalranges_1' mint_0 mint_1 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 (shift a i) = mint_0 (shift b i))" for mint_0 mint_1 a n b
definition p_equal :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> _"
  where "p_equal mptr_0 mint_0 mptr_1 mint_1 s t \<longleftrightarrow> (let x :: int = l_size mint_1 s in l_size mint_0 t = x \<and> p_equalranges_1' mint_0 mint_1 (l_storage mptr_1 s) x (l_storage mptr_0 t))" for mptr_0 mint_0 mptr_1 mint_1 s t
definition l_capacity :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
  where "l_capacity mint_0 s = mint_0 (shift s (1 :: int))" for mint_0 s
definition p_invariant :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_invariant malloc_0 mptr_0 mint_0 s \<longleftrightarrow> (let x :: int = l_capacity mint_0 s; x_1 :: int = l_size mint_0 s; a :: addr = shift (l_storage mptr_0 s) (0 :: int) in (0 :: int) < x \<and> x_1 \<le> x \<and> (0 :: int) \<le> x_1 \<and> valid_rw malloc_0 a x \<and> separated s (3 :: int) a x)" for malloc_0 mptr_0 mint_0 s
definition p_empty :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_empty mint_0 s \<longleftrightarrow> l_size mint_0 s = (0 :: int)" for mint_0 s
definition p_unchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_unchanged_1' mint_0 mint_1 a m n \<longleftrightarrow> (\<forall>(i :: int). let a_1 :: addr = shift a i in m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 a_1 = mint_0 a_1)" for mint_0 mint_1 a m n
definition p_full :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_full mint_0 s \<longleftrightarrow> l_size mint_0 s = l_capacity mint_0 s" for mint_0 s
definition l_top :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
  where "l_top mptr_0 mint_0 s = mint_0 (shift (mptr_0 (shift s (0 :: int))) (mint_0 (shift s (2 :: int)) - (1 :: int)))" for mptr_0 mint_0 s
axiomatization where Q_TL_Size:   "is_uint32 (l_size mint_0 s)"
  for mint_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
axiomatization where Q_TL_Capacity:   "is_uint32 (l_capacity mint_0 s)"
  for mint_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
axiomatization where Q_TL_Top:   "is_sint32 (l_top mptr_0 mint_0 s)"
  for mptr_0 :: "addr \<Rightarrow> addr"
  and mint_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
end
