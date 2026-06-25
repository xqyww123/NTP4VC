theory lemma_functions_LemmaFunction2_sum_nonnegqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum"
begin
theorem sum_nonneg'vc:
  fixes l :: "int"
  fixes u :: "int"
  fixes a :: "int list"
  assumes fact0: "(0 :: int) \<le> l"
  assumes fact1: "l \<le> u"
  assumes fact2: "u \<le> int (length a)"
  assumes fact3: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> (0 :: int) \<le> a ! nat i"
  shows "(0 :: int) \<le> sum_list (take (nat u - nat l) (drop (nat l) a))"
  sorry
end
