theory verifythis_2021_lexicographic_permutations_2_ArrayListConversions_to_listqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_MapEq"
begin
consts to_list_from :: "int \<Rightarrow> int list \<Rightarrow> int list"
axiomatization where to_list_from_def:   "if i = int (length a) then to_list_from i a = (Nil :: int list) else to_list_from i a = Cons (a ! nat i) (to_list_from (i + (1 :: int)) a)"
 if "(0 :: int) \<le> i"
 and "i \<le> int (length a)"
  for i :: "int"
  and a :: "int list"
axiomatization where to_list_from'spec'0:   "int (length (to_list_from i a)) = int (length a) - i"
 if "(0 :: int) \<le> i"
 and "i \<le> int (length a)"
  for i :: "int"
  and a :: "int list"
axiomatization where to_list_from'spec:   "nth_opt (to_list_from i a) k = Some (a ! nat (k + i))"
 if "(0 :: int) \<le> i"
 and "i \<le> int (length a)"
 and "(0 :: int) \<le> k"
 and "k < int (length a) - i"
  for i :: "int"
  and a :: "int list"
  and k :: "int"
theorem to_list'vc:
  fixes a :: "int list"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length a)"
  sorry
end
