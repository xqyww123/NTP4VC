theory hashtbl_impl_HashtblImpl_list_removeqtvc
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
theorem list_remove'vc:
  fixes l :: "(key \<times> 'a) list"
  fixes k :: "key"
  fixes p :: "key \<times> 'a"
  shows "case l of (Nil :: (key \<times> 'a) list) \<Rightarrow> True | Cons (k', x) r \<Rightarrow> (let p = (k', x) in (case l of (Nil :: (key \<times> 'a) list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = r))"
  and "\<forall>(result :: (key \<times> 'a) list). (case l of (Nil :: (key \<times> 'a) list) \<Rightarrow> result = (Nil :: (key \<times> 'a) list) | Cons (k', x) r \<Rightarrow> (let p = (k', x) in if k = k' then \<forall>(k'1 :: key) (v :: 'a). (k'1, v) \<in> set result \<longleftrightarrow> (k'1, v) \<in> set r \<and> \<not>k'1 = k else \<exists>(o1 :: (key \<times> 'a) list). (\<forall>(k'1 :: key) (v :: 'a). (k'1, v) \<in> set o1 \<longleftrightarrow> (k'1, v) \<in> set r \<and> \<not>k'1 = k) \<and> result = Cons p o1)) \<longrightarrow> (\<forall>(k' :: key) (v :: 'a). (k', v) \<in> set result \<longleftrightarrow> (k', v) \<in> set l \<and> \<not>k' = k)"
  sorry
end
