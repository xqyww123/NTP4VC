theory string_search_BadShiftTable_shift_lemmaqtvc
  imports "NTP4Verif.NTP4Verif" "./string_search_Spec" "./string_search_Occurs" "Why3STD.ocaml_Exceptions"
begin
typedecl 'v t
consts to_fmap :: "'v t \<Rightarrow> (char, 'v) fmap"
typedecl  bad_shift_table
consts pat :: "bad_shift_table \<Rightarrow> string"
consts sht :: "bad_shift_table \<Rightarrow> 63 word t"
axiomatization where bad_shift_table'invariant'0:   "\<forall>(j :: int) (c :: char). (0 :: int) \<le> j \<and> j < int (length (pat self)) \<longrightarrow> c = pat self ! nat j \<longrightarrow> c |\<in>| fmdom (to_fmap (sht self))"
  for self :: "bad_shift_table"
axiomatization where bad_shift_table'invariant'1:   "\<forall>(c :: char). c |\<in>| fmdom (to_fmap (sht self)) \<longrightarrow> (1 :: int) \<le> sint (fm_contents (to_fmap (sht self)) c) \<and> sint (fm_contents (to_fmap (sht self)) c) \<le> int (length (pat self)) + (1 :: int)"
  for self :: "bad_shift_table"
axiomatization where bad_shift_table'invariant'2:   "\<forall>(c :: char). c |\<in>| fmdom (to_fmap (sht self)) \<longrightarrow> (\<forall>(j :: int). (1 :: int) \<le> j \<and> j < sint (fm_contents (to_fmap (sht self)) c) \<longrightarrow> \<not>pat self ! nat (int (length (pat self)) - j) = c)"
  for self :: "bad_shift_table"
definition bad_shift_table'eq :: "bad_shift_table \<Rightarrow> bad_shift_table \<Rightarrow> _"
  where "bad_shift_table'eq a b \<longleftrightarrow> pat a = pat b \<and> sht a = sht b" for a b
axiomatization where bad_shift_table'inj:   "a = b"
 if "bad_shift_table'eq a b"
  for a :: "bad_shift_table"
  and b :: "bad_shift_table"
theorem shift_lemma'vc:
  fixes i :: "63 word"
  fixes "text" :: "string"
  fixes bst :: "bad_shift_table"
  fixes j :: "int"
  assumes fact0: "(0 :: int) \<le> sint i"
  assumes fact1: "sint i \<le> int (length text) - int (length (pat bst))"
  assumes fact2: "text ! nat (sint i + int (length (pat bst))) |\<in>| fmdom (to_fmap (sht bst))"
  assumes fact3: "sint i < j"
  assumes fact4: "j < sint i + sint (the (fmlookup (to_fmap (sht bst)) (text ! nat (sint i + int (length (pat bst))))))"
  assumes fact5: "j \<le> int (length text) - int (length (pat bst))"
  shows "\<not>substring text j (int (length (pat bst))) = pat bst"
  sorry
end
