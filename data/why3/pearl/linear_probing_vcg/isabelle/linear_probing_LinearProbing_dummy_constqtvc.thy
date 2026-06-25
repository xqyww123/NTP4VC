theory linear_probing_LinearProbing_dummy_constqtvc
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
theorem dummy_const'vc:
  fixes n :: "int"
  fixes a :: "key list"
  assumes fact0: "(0 :: int) \<le> n"
  assumes fact1: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> a ! nat i = dummy"
  shows "numof a (0 :: int) n = n"
  sorry
end
