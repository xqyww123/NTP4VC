theory hashtbl_impl_HashtblImpl_resizeqtvc
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
theorem resize'vc:
  fixes h :: "'a t"
  shows "let odata :: (key \<times> 'a) list list = data h; osize :: int = int (length odata); nsize :: int = (2 :: int) * osize + (1 :: int) in (0 :: int) \<le> nsize \<and> (\<forall>(ndata :: (key \<times> 'a) list list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < nsize \<longrightarrow> ndata ! nat i = (Nil :: (key \<times> 'a) list)) \<and> int (length ndata) = nsize \<longrightarrow> (\<forall>(ndata1 :: (key \<times> 'a) list list) (h1 :: 'a t). length ndata1 = length ndata \<longrightarrow> (\<forall>(i :: int) (l :: (key \<times> 'a) list). (view h = view h1 \<and> size h = size h1) \<and> (\<forall>(k :: key) (v :: 'a). (k, v) \<in> set l \<longrightarrow> bucket k osize = i) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata1 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < i then good_data k v (view h1) ndata1 else if bucket k osize = i then view h1 k = Some v \<longleftrightarrow> (k, v) \<in> set l \<or> in_data k v ndata1 else \<not>in_data k v ndata1) \<longrightarrow> (case l of (Nil :: (key \<times> 'a) list) \<Rightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata1 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize \<le> i then good_data k v (view h1) ndata1 else \<not>in_data k v ndata1) | Cons (k, v) r \<Rightarrow> (0 :: int) < nsize \<and> (let b :: int = bucket k nsize in (0 :: int) \<le> b \<and> b < nsize \<longrightarrow> ((0 :: int) \<le> b \<and> b < int (length ndata1)) \<and> (let o1 :: (key \<times> 'a) list = Cons (k, v) (ndata1 ! nat b) in ((0 :: int) \<le> b \<and> b < int (length ndata1)) \<and> (length (ndata1[nat b := o1]) = length ndata1 \<longrightarrow> nth (ndata1[nat b := o1]) o nat = (nth ndata1 o nat)(b := o1) \<longrightarrow> (case l of (Nil :: (key \<times> 'a) list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = r) \<and> (\<forall>(k1 :: key) (v1 :: 'a). (k1, v1) \<in> set r \<longrightarrow> bucket k1 osize = i) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash (ndata1[nat b := o1]) j) \<and> (\<forall>(k1 :: key) (v1 :: 'a). if (0 :: int) \<le> bucket k1 osize \<and> bucket k1 osize < i then good_data k1 v1 (view h1) (ndata1[nat b := o1]) else if bucket k1 osize = i then view h1 k1 = Some v1 \<longleftrightarrow> (k1, v1) \<in> set r \<or> in_data k1 v1 (ndata1[nat b := o1]) else \<not>in_data k1 v1 (ndata1[nat b := o1])))))))) \<and> (let o1 :: int = osize - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < (0 :: int) then good_data k v (view h) ndata else \<not>in_data k v ndata)) \<and> (\<forall>(ndata1 :: (key \<times> 'a) list list). length ndata1 = length ndata \<longrightarrow> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o1) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata1 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < i then good_data k v (view h) ndata1 else \<not>in_data k v ndata1) \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (length odata)) \<and> (let o2 :: (key \<times> 'a) list = odata ! nat i in ((\<forall>(k :: key) (v :: 'a). (k, v) \<in> set o2 \<longrightarrow> bucket k osize = i) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata1 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < i then good_data k v (view h) ndata1 else if bucket k osize = i then view h k = Some v \<longleftrightarrow> (k, v) \<in> set o2 \<or> in_data k v ndata1 else \<not>in_data k v ndata1)) \<and> (\<forall>(ndata2 :: (key \<times> 'a) list list). length ndata2 = length ndata1 \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata2 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize \<le> i then good_data k v (view h) ndata2 else \<not>in_data k v ndata2) \<longrightarrow> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata2 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < i + (1 :: int) then good_data k v (view h) ndata2 else \<not>in_data k v ndata2)))) \<and> ((\<forall>(j :: int). (0 :: int) \<le> j \<and> j < nsize \<longrightarrow> good_hash ndata1 j) \<and> (\<forall>(k :: key) (v :: 'a). if (0 :: int) \<le> bucket k osize \<and> bucket k osize < o1 + (1 :: int) then good_data k v (view h) ndata1 else \<not>in_data k v ndata1) \<longrightarrow> (0 :: int) < int (length ndata1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length ndata1) \<longrightarrow> good_hash ndata1 i) \<and> (\<forall>(k :: key) (v :: 'a). good_data k v (view h) ndata1)))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> (0 :: int) < int (length ndata) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length ndata) \<longrightarrow> good_hash ndata i) \<and> (\<forall>(k :: key) (v :: 'a). good_data k v (view h) ndata))))"
  sorry
end
