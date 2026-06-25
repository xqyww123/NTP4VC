theory hashtbl_impl_HashtblImpl_tqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const"
begin
typedecl  key
consts hash :: "key \<Rightarrow> int"
axiomatization where hash'spec:   "(0 :: int) \<le> hash x"
  for x :: "key"
consts bucket :: "key \<Rightarrow> int \<Rightarrow> int"
axiomatization where bucket_def:   "bucket k n = hash k cmod n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
axiomatization where bucket'spec'0:   "(0 :: int) \<le> bucket k n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
axiomatization where bucket'spec'1:   "bucket k n < n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
definition in_data :: "key \<Rightarrow> 'a \<Rightarrow> (key \<times> 'a) list list \<Rightarrow> _"
  where "in_data k v d \<longleftrightarrow> (k, v) \<in> set (d ! nat (bucket k (int (length d))))" for k v d
definition good_data :: "key \<Rightarrow> 'a \<Rightarrow> (key \<Rightarrow> 'a option) \<Rightarrow> (key \<times> 'a) list list \<Rightarrow> _"
  where "good_data k v m d \<longleftrightarrow> m k = Some v \<longleftrightarrow> in_data k v d" for k v m d
definition good_hash :: "(key \<times> 'a) list list \<Rightarrow> int \<Rightarrow> _"
  where "good_hash d i \<longleftrightarrow> (\<forall>(k :: key) (v :: 'a). (k, v) \<in> set (d ! nat i) \<longrightarrow> bucket k (int (length d)) = i)" for d i
theorem t'vc:
  shows "(0 :: int) \<le> (1 :: int)"
  and "\<forall>(o1 :: (key \<times> 'a) list list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (1 :: int) \<longrightarrow> o1 ! nat i = (Nil :: (key \<times> 'a) list)) \<and> int (length o1) = (1 :: int) \<longrightarrow> (0 :: int) < int (length o1) \<and> ((0 :: int) < int (length o1) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length o1) \<longrightarrow> good_hash o1 i) \<and> ((\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length o1) \<longrightarrow> good_hash o1 i) \<longrightarrow> (\<forall>(k :: key) (v :: 'a). good_data k v ((const :: 'a option \<Rightarrow> key \<Rightarrow> 'a option) (None :: 'a option)) o1)))"
  sorry
end
