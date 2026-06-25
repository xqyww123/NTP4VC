theory string_search_Occurs_occursqtvc
  imports "NTP4Verif.NTP4Verif" "./string_search_Spec"
begin
theorem occurs'vc:
  fixes p :: "63 word"
  fixes "text" :: "string"
  fixes pat :: "string"
  fixes n :: "63 word"
  fixes m :: "63 word"
  assumes fact0: "(0 :: int) \<le> sint p"
  assumes fact1: "sint p \<le> int (length text) - int (length pat)"
  assumes fact2: "sint n = int (length text)"
  assumes fact3: "(0 :: int) \<le> int (length text)"
  assumes fact4: "sint m = int (length pat)"
  assumes fact5: "(0 :: int) \<le> int (length pat)"
  shows "int'63_in_bounds (sint m - (1 :: int))"
  and "\<forall>(o1 :: 63 word). sint o1 = sint m - (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint o1 + (1 :: int) \<longrightarrow> drop (nat (sint p)) (take ((0 :: nat) - nat (sint p)) text) = drop (0 :: nat) (take ((0 :: nat) - (0 :: nat)) pat) \<and> (\<forall>(i :: 63 word). let i1 :: int = sint i in ((0 :: int) \<le> i1 \<and> i1 \<le> sint o1) \<and> take (nat i1 - nat (sint p)) (drop (nat (sint p)) text) = drop (0 :: nat) (take (nat i1 - (0 :: nat)) pat) \<longrightarrow> ((0 :: int) \<le> sint i \<and> sint i < int (length pat)) \<and> int'63_in_bounds (sint p + sint i) \<and> (\<forall>(o2 :: 63 word). sint o2 = sint p + sint i \<longrightarrow> ((0 :: int) \<le> sint o2 \<and> sint o2 < int (length text)) \<and> (if \<not>text ! nat (sint o2) = pat ! nat (sint i) then \<not>matches1 pat text (sint p) else take (nat (i1 + (1 :: int)) - nat (sint p)) (drop (nat (sint p)) text) = drop (0 :: nat) (take (nat (i1 + (1 :: int)) - (0 :: nat)) pat)))) \<and> (take (nat (sint o1 + (1 :: int)) - nat (sint p)) (drop (nat (sint p)) text) = drop (0 :: nat) (take (nat (sint o1 + (1 :: int)) - (0 :: nat)) pat) \<longrightarrow> matches1 pat text (sint p))) \<and> (sint o1 + (1 :: int) < (0 :: int) \<longrightarrow> matches1 pat text (sint p))"
  sorry
end
