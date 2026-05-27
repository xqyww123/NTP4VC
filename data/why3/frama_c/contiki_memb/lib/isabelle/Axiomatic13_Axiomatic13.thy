theory Axiomatic13_Axiomatic13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "A_OccArray_A_OccArray"
begin
definition p_valid_memb :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_valid_memb malloc_0 mptr_0 mint_0 m \<longleftrightarrow> (let x :: int = mint_0 (shift m (0 :: int)); x_1 :: int = mint_0 (shift m (1 :: int)); x_2 :: int = x_1 * x; a :: addr = mptr_0 (shift m (2 :: int)); a_1 :: addr = mptr_0 (shift m (3 :: int)); a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int) in (0 :: int) < x \<and> x_2 \<le> (2147483647 :: int) \<and> valid_rw malloc_0 m (4 :: int) \<and> valid_rw malloc_0 a (1 :: int) \<and> valid_rw malloc_0 a_1 (1 :: int) \<and> valid_rw malloc_0 a_2 x_1 \<and> valid_rw malloc_0 a_3 x_2 \<and> separated a_2 x_1 a_3 x_2)" for malloc_0 mptr_0 mint_0 m
definition p__memb_full :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p__memb_full mptr_0 mchar_0 mint_0 m \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < mint_0 (shift m (1 :: int)) \<longrightarrow> \<not>mchar_0 (shift (mptr_0 (shift m (2 :: int))) i) = (0 :: int))" for mptr_0 mchar_0 mint_0 m
definition l__memb_index :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int"
  where "l__memb_index mptr_0 mint_0 m ptr_0 = (offset ptr_0 - offset (mptr_0 (shift m (3 :: int)))) cdiv mint_0 (shift m (0 :: int))" for mptr_0 mint_0 m ptr_0
definition l__memb_ptr :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr"
  where "l__memb_ptr mptr_0 mint_0 m index_0 = shift (mptr_0 (shift m (3 :: int))) (index_0 * mint_0 (shift m (0 :: int)))" for mptr_0 mint_0 m index_0
definition p__memb_has :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> _"
  where "p__memb_has mptr_0 mint_0 m ptr_0 \<longleftrightarrow> (\<exists>(i :: int). l__memb_ptr mptr_0 mint_0 m i = ptr_0 \<and> (0 :: int) \<le> i \<and> i < mint_0 (shift m (1 :: int)))" for mptr_0 mint_0 m ptr_0
definition p__memb_allocated :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> _"
  where "p__memb_allocated mptr_0 mchar_0 mint_0 m ptr_0 \<longleftrightarrow> \<not>mchar_0 (shift (mptr_0 (shift m (2 :: int))) (l__memb_index mptr_0 mint_0 m ptr_0)) = (0 :: int) \<and> p__memb_has mptr_0 mint_0 m ptr_0" for mptr_0 mchar_0 mint_0 m ptr_0
definition l__memb_numfree :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
  where "l__memb_numfree mptr_0 mchar_0 mint_0 m = l_occ_a mchar_0 (0 :: int) (mptr_0 (shift m (2 :: int))) (0 :: int) (mint_0 (shift m (1 :: int)))" for mptr_0 mchar_0 mint_0 m
definition p__memb_empty :: "(addr \<Rightarrow> addr) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p__memb_empty mptr_0 mchar_0 mint_0 m \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < mint_0 (shift m (1 :: int)) \<longrightarrow> mchar_0 (shift (mptr_0 (shift m (2 :: int))) i) = (0 :: int))" for mptr_0 mchar_0 mint_0 m
axiomatization where Q_mult_simplification:   "a * b cdiv b = a"
 if "(0 :: int) < b"
 and "(0 :: int) \<le> a"
  for b :: "int"
  and a :: "int"
end
