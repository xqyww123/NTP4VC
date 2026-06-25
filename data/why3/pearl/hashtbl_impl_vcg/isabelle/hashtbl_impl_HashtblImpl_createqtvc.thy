theory hashtbl_impl_HashtblImpl_createqtvc
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
typedecl 'a t
consts size :: "'a t \<Rightarrow> int"
consts data :: "'a t \<Rightarrow> (key \<times> 'a) list list"
consts view :: "'a t \<Rightarrow> key \<Rightarrow> 'a option"
axiomatization where t'invariant'0:   "(0 :: int) < int (length (data self))"
  for self :: "'a t"
axiomatization where t'invariant'1:   "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length (data self)) \<longrightarrow> good_hash (data self) i"
  for self :: "'a t"
axiomatization where t'invariant'2:   "\<forall>(k :: key) (v :: 'a). good_data k v (view self) (data self)"
  for self :: "'a t"
definition t'eq :: "'a t \<Rightarrow> 'a t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> size a = size b \<and> data a = data b \<and> view a = view b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t"
  and b :: "'a t"
theorem create'vc:
  fixes n :: "int"
  assumes fact0: "(1 :: int) \<le> n"
  shows "let o1 :: key \<Rightarrow> 'a option = (const :: 'a option \<Rightarrow> key \<Rightarrow> 'a option) (None :: 'a option) in (0 :: int) \<le> n \<and> (\<forall>(o2 :: (key \<times> 'a) list list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> o2 ! nat i = (Nil :: (key \<times> 'a) list)) \<and> int (length o2) = n \<longrightarrow> ((0 :: int) < int (length o2) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length o2) \<longrightarrow> good_hash o2 i) \<and> (\<forall>(k :: key) (v :: 'a). good_data k v o1 o2)) \<and> (\<forall>(result :: 'a t). size result = (0 :: int) \<and> data result = o2 \<and> view result = o1 \<longrightarrow> view result = (const :: 'a option \<Rightarrow> key \<Rightarrow> 'a option) (None :: 'a option)))"
  sorry
end
