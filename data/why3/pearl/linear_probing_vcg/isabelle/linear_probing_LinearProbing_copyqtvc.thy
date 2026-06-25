theory linear_probing_LinearProbing_copyqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "Why3STD.map_Const"
begin
typedecl  key
typedecl  keym
consts keym1 :: "key \<Rightarrow> keym"
consts eq :: "key \<Rightarrow> key \<Rightarrow> bool"
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> keym1 x = keym1 y"
  for x :: "key"
  and y :: "key"
definition neq :: "key \<Rightarrow> key \<Rightarrow> _"
  where "neq x y \<longleftrightarrow> \<not>eq x y" for x y
axiomatization where neq'spec:   "neq x y \<longleftrightarrow> \<not>keym1 x = keym1 y"
  for x :: "key"
  and y :: "key"
consts hash :: "key \<Rightarrow> int"
axiomatization where hash_nonneg:   "(0 :: int) \<le> hash k"
  for k :: "key"
axiomatization where hash_eq:   "hash x = hash y"
 if "eq x y"
  for x :: "key"
  and y :: "key"
consts dummy :: "key"
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
definition between :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "between l j r \<longleftrightarrow> l \<le> j \<and> j < r \<or> r < l \<and> l \<le> j \<or> j < r \<and> r < l" for l j r
consts fc :: "key list \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc a i = True \<longleftrightarrow> eq (a ! nat i) dummy"
  for a :: "key list"
  and i :: "int"
definition numof :: "key list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numof a l u = int_NumOf.numof (fc a) l u" for a l u
definition valid :: "key list \<Rightarrow> (keym \<Rightarrow> bool) \<Rightarrow> (keym \<Rightarrow> int) \<Rightarrow> _"
  where "valid data view loc \<longleftrightarrow> \<not>view (keym1 dummy) = True \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length data) \<longrightarrow> (let x :: key = data ! nat i in neq x dummy \<longrightarrow> view (keym1 x) = True \<and> loc (keym1 x) = i)) \<and> (let n :: int = int (length data) in \<forall>(x :: key). view (keym1 x) = True \<longrightarrow> (let i :: int = loc (keym1 x) in ((0 :: int) \<le> i \<and> i < n) \<and> eq (data ! nat i) x \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n \<longrightarrow> between (bucket x n) j i \<longrightarrow> neq (data ! nat j) x \<and> neq (data ! nat j) dummy)))" for data view loc
typedecl  t
consts size :: "t \<Rightarrow> int"
consts data :: "t \<Rightarrow> key list"
consts view :: "t \<Rightarrow> keym \<Rightarrow> bool"
consts loc :: "t \<Rightarrow> keym \<Rightarrow> int"
axiomatization where t'invariant'0:   "(0 :: int) \<le> size self"
  for self :: "t"
axiomatization where t'invariant'1:   "size self < int (length (data self))"
  for self :: "t"
axiomatization where t'invariant'2:   "size self + numof (data self) (0 :: int) (int (length (data self))) = int (length (data self))"
  for self :: "t"
axiomatization where t'invariant'3:   "valid (data self) (view self) (loc self)"
  for self :: "t"
definition t'eq :: "t \<Rightarrow> t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> size a = size b \<and> data a = data b \<and> view a = view b \<and> loc a = loc b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "t"
  and b :: "t"
definition "next" :: "int \<Rightarrow> int \<Rightarrow> int"
  where "next n i = (let i1 :: int = i + (1 :: int) in if i1 = n then 0 :: int else i1)" for n i
theorem copy'vc:
  fixes h :: "t"
  shows "let o1 :: keym \<Rightarrow> int = loc h; o2 :: keym \<Rightarrow> bool = view h; o3 :: key list = data h in \<forall>(o4 :: key list). length o4 = length o3 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length o4) \<longrightarrow> o4 ! nat i = o3 ! nat i) \<longrightarrow> (let o5 :: int = size h in (((0 :: int) \<le> o5 \<and> o5 < int (length o4)) \<and> (let n :: int = int (length o4) in o5 + numof o4 (0 :: int) n = n) \<and> valid o4 o2 o1) \<and> (\<forall>(result :: t). size result = o5 \<and> data result = o4 \<and> view result = o2 \<and> loc result = o1 \<longrightarrow> view result = view h))"
  sorry
end
