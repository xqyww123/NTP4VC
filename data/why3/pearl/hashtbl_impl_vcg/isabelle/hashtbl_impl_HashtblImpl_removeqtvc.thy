theory hashtbl_impl_HashtblImpl_removeqtvc
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
theorem remove'vc:
  fixes h :: "'a t"
  fixes k :: "key"
  shows "let o1 :: int = int (length (data h)) in (0 :: int) < o1 \<and> (let i :: int = bucket k o1 in (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> (let o2 :: (key \<times> 'a) list list = data h in ((0 :: int) \<le> i \<and> i < int (length o2)) \<and> (let l :: (key \<times> 'a) list = o2 ! nat i in \<forall>(o3 :: 'a option). (case o3 of (None :: 'a option) \<Rightarrow> (\<forall>(v :: 'a). \<not>(k, v) \<in> set l) | Some v \<Rightarrow> (k, v) \<in> set l) \<longrightarrow> (case o3 of (None :: 'a option) \<Rightarrow> view h k = (None :: 'a option) | Some _ \<Rightarrow> (\<forall>(o4 :: (key \<times> 'a) list). (\<forall>(k' :: key) (v :: 'a). (k', v) \<in> set o4 \<longleftrightarrow> (k', v) \<in> set l \<and> \<not>k' = k) \<longrightarrow> (let o5 :: (key \<times> 'a) list list = data h in ((0 :: int) \<le> i \<and> i < int (length o5)) \<and> (length (o5[nat i := o4]) = length o5 \<longrightarrow> length (o5[nat i := o4]) = length (data h) \<longrightarrow> nth (o5[nat i := o4]) o nat = (nth o5 o nat)(i := o4) \<longrightarrow> (\<forall>(h1 :: 'a t). ((0 :: int) < int (length (o5[nat i := o4])) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < int (length (o5[nat i := o4])) \<longrightarrow> good_hash (o5[nat i := o4]) i1) \<and> (\<forall>(k1 :: key) (v :: 'a). good_data k1 v ((view h)(k := (None :: 'a option))) (o5[nat i := o4]))) \<and> ((view h)(k := (None :: 'a option)) = view h1 \<and> o5[nat i := o4] = data h1 \<and> size h - (1 :: int) = size h1 \<longrightarrow> view h1 k = (None :: 'a option) \<and> (\<forall>(k' :: key). \<not>k' = k \<longrightarrow> view h1 k' = view h k'))))))))))"
  sorry
end
