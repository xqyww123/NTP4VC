theory verifythis_2021_lexicographic_permutations_2_ArrayListConversions_of_listqtvc
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
theorem of_list'vc:
  fixes l :: "int list"
  shows "let o1 :: int = int (length l) in (0 :: int) \<le> o1 \<and> (\<forall>(a :: int list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> a ! nat i = (0 :: int)) \<and> int (length a) = o1 \<longrightarrow> (\<forall>(a1 :: int list). length a1 = length a \<longrightarrow> (\<forall>(l' :: int list) (i :: int). (0 :: int) \<le> i \<and> int (length l') = int (length l) - i \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length l') \<longrightarrow> nth_opt l (k + i) = nth_opt l' k) \<longrightarrow> (case l' of Nil \<Rightarrow> (\<forall>(k :: int). i \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l k = Some (a1 ! nat k)) | Cons v t \<Rightarrow> ((0 :: int) \<le> i \<and> i < int (length a1)) \<and> (length (a1[nat i := v]) = length a1 \<longrightarrow> nth (a1[nat i := v]) o nat = (nth a1 o nat)(i := v) \<longrightarrow> (let o2 :: int = i + (1 :: int) in ((case l' of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = t) \<and> (0 :: int) \<le> o2 \<and> int (length t) = int (length l) - o2 \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length t) \<longrightarrow> nth_opt l (k + o2) = nth_opt t k)) \<and> (\<forall>(a2 :: int list). length a2 = length (a1[nat i := v]) \<longrightarrow> (\<forall>(k :: int). o2 \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l k = Some (a2 ! nat k)) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < o2 \<longrightarrow> a2 ! nat k = a1[nat i := v] ! nat k) \<longrightarrow> (\<forall>(k :: int). i \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l k = Some (a2 ! nat k)) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < i \<longrightarrow> a2 ! nat k = a1 ! nat k))))))) \<and> ((0 :: int) \<le> (0 :: int) \<and> int (length l) = int (length l) - (0 :: int) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l (k + (0 :: int)) = nth_opt l k)) \<and> (\<forall>(a1 :: int list). length a1 = length a \<longrightarrow> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l k = Some (a1 ! nat k)) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < (0 :: int) \<longrightarrow> a1 ! nat k = a ! nat k) \<longrightarrow> length a1 = length l \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length l) \<longrightarrow> nth_opt l k = Some (a1 ! nat k))))"
  sorry
end
