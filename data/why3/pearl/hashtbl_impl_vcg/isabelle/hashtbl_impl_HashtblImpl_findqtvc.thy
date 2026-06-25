theory hashtbl_impl_HashtblImpl_findqtvc
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
theorem find'vc:
  fixes h :: "'a t"
  fixes k :: "key"
  shows "let o1 :: int = int (length (data h)) in (0 :: int) < o1 \<and> (let i :: int = bucket k o1 in (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> (let o2 :: (key \<times> 'a) list list = data h in ((0 :: int) \<le> i \<and> i < int (length o2)) \<and> (let o3 :: (key \<times> 'a) list = o2 ! nat i in \<forall>(result :: 'a option). (case result of (None :: 'a option) \<Rightarrow> (\<forall>(v :: 'a). \<not>(k, v) \<in> set o3) | Some v \<Rightarrow> (k, v) \<in> set o3) \<longrightarrow> result = view h k)))"
  sorry
end
