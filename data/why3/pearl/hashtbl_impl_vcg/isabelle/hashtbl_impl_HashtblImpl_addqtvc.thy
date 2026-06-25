theory hashtbl_impl_HashtblImpl_addqtvc
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
theorem add'vc:
  fixes h :: "'a t"
  fixes k :: "key"
  fixes v :: "'a"
  shows "if size h = int (length (data h)) then \<forall>(h1 :: 'a t). view h = view h1 \<and> size h = size h1 \<longrightarrow> (\<forall>(h2 :: 'a t). length (data h2) = length (data h1) \<longrightarrow> view h2 k = (None :: 'a option) \<and> (\<forall>(k' :: key). \<not>k' = k \<longrightarrow> view h2 k' = view h1 k') \<longrightarrow> (let o1 :: int = int (length (data h2)) in (0 :: int) < o1 \<and> (let i :: int = bucket k o1 in (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> (let o2 :: (key \<times> 'a) list list = data h2 in ((0 :: int) \<le> i \<and> i < int (length o2)) \<and> (let o3 :: (key \<times> 'a) list = Cons (k, v) (o2 ! nat i); o4 :: (key \<times> 'a) list list = data h2 in ((0 :: int) \<le> i \<and> i < int (length o4)) \<and> (length (o4[nat i := o3]) = length o4 \<longrightarrow> length (o4[nat i := o3]) = length (data h2) \<longrightarrow> nth (o4[nat i := o3]) o nat = (nth o4 o nat)(i := o3) \<longrightarrow> (\<forall>(h3 :: 'a t). ((0 :: int) < int (length (o4[nat i := o3])) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < int (length (o4[nat i := o3])) \<longrightarrow> good_hash (o4[nat i := o3]) i1) \<and> (\<forall>(k1 :: key) (v1 :: 'a). good_data k1 v1 ((view h2)(k := Some v)) (o4[nat i := o3]))) \<and> ((view h2)(k := Some v) = view h3 \<and> o4[nat i := o3] = data h3 \<and> size h2 + (1 :: int) = size h3 \<longrightarrow> view h3 k = Some v \<and> (\<forall>(k' :: key). \<not>k' = k \<longrightarrow> view h3 k' = view h k'))))))))) else \<forall>(h1 :: 'a t). length (data h1) = length (data h) \<longrightarrow> view h1 k = (None :: 'a option) \<and> (\<forall>(k' :: key). \<not>k' = k \<longrightarrow> view h1 k' = view h k') \<longrightarrow> (let o1 :: int = int (length (data h1)) in (0 :: int) < o1 \<and> (let i :: int = bucket k o1 in (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> (let o2 :: (key \<times> 'a) list list = data h1 in ((0 :: int) \<le> i \<and> i < int (length o2)) \<and> (let o3 :: (key \<times> 'a) list = Cons (k, v) (o2 ! nat i); o4 :: (key \<times> 'a) list list = data h1 in ((0 :: int) \<le> i \<and> i < int (length o4)) \<and> (length (o4[nat i := o3]) = length o4 \<longrightarrow> length (o4[nat i := o3]) = length (data h1) \<longrightarrow> nth (o4[nat i := o3]) o nat = (nth o4 o nat)(i := o3) \<longrightarrow> (\<forall>(h2 :: 'a t). ((0 :: int) < int (length (o4[nat i := o3])) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < int (length (o4[nat i := o3])) \<longrightarrow> good_hash (o4[nat i := o3]) i1) \<and> (\<forall>(k1 :: key) (v1 :: 'a). good_data k1 v1 ((view h1)(k := Some v)) (o4[nat i := o3]))) \<and> ((view h1)(k := Some v) = view h2 \<and> o4[nat i := o3] = data h2 \<and> size h1 + (1 :: int) = size h2 \<longrightarrow> view h2 k = Some v \<and> (\<forall>(k' :: key). \<not>k' = k \<longrightarrow> view h2 k' = view h k'))))))))"
  sorry
end
