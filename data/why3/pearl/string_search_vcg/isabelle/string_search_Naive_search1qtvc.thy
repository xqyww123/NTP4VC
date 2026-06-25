theory string_search_Naive_search1qtvc
  imports "NTP4Verif.NTP4Verif" "./string_search_Spec" "./string_search_Occurs"
begin
theorem search1'vc:
  fixes pat :: "string"
  fixes "text" :: "string"
  fixes m :: "63 word"
  fixes n :: "63 word"
  assumes fact0: "length pat \<le> length text"
  assumes fact1: "sint m = int (length pat)"
  assumes fact2: "(0 :: int) \<le> int (length pat)"
  assumes fact3: "sint n = int (length text)"
  assumes fact4: "(0 :: int) \<le> int (length text)"
  shows "int'63_in_bounds (sint n - sint m)"
  and "\<forall>(o1 :: 63 word). sint o1 = sint n - sint m \<longrightarrow> ((0 :: int) \<le> sint o1 + (1 :: int) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> \<not>take (nat (sint m) - nat j) (drop (nat j) text) = pat) \<and> (\<forall>(i :: 63 word). let i1 :: int = sint i in ((0 :: int) \<le> i1 \<and> i1 \<le> sint o1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < i1 \<longrightarrow> \<not>take (nat (sint m) - nat j) (drop (nat j) text) = pat) \<longrightarrow> ((0 :: int) \<le> sint i \<and> sint i \<le> int (length text) - int (length pat)) \<and> (if matches1 pat text (sint i) then (-(1 :: int) \<le> sint i \<and> sint i \<le> int (length text) - int (length pat)) \<and> (if sint i = -(1 :: int) then \<forall>(j :: int). \<not>matches1 pat text j else matches1 pat text (sint i)) else \<forall>(j :: int). (0 :: int) \<le> j \<and> j < i1 + (1 :: int) \<longrightarrow> \<not>take (nat (sint m) - nat j) (drop (nat j) text) = pat)) \<and> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint o1 + (1 :: int) \<longrightarrow> \<not>take (nat (sint m) - nat j) (drop (nat j) text) = pat) \<longrightarrow> (-(1 :: int) \<le> -(1 :: int) \<and> -(1 :: int) \<le> int (length text) - int (length pat)) \<and> (\<forall>(j :: int). \<not>matches1 pat text j))) \<and> (sint o1 + (1 :: int) < (0 :: int) \<longrightarrow> (-(1 :: int) \<le> -(1 :: int) \<and> -(1 :: int) \<le> int (length text) - int (length pat)) \<and> (\<forall>(j :: int). \<not>matches1 pat text j))"
  sorry
end
