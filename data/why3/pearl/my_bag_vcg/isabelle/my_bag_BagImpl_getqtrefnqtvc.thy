theory my_bag_BagImpl_getqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf" "Why3STD.map_Const" "./my_bag_Bag" "./my_bag_ResizableArraySpec"
begin
consts fc :: "'a rarray \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc r x i = True \<longleftrightarrow> data r i = x"
  for r :: "'a rarray"
  and x :: "'a"
  and i :: "int"
definition numof :: "'a rarray \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numof r x l u = int_NumOf.numof (fc r x) l u" for r x l u
typedecl 'a t
consts size :: "'a t \<Rightarrow> int"
consts data :: "'a t \<Rightarrow> 'a rarray"
consts contents :: "'a t \<Rightarrow> 'a \<Rightarrow> int"
axiomatization where t'invariant'0:   "(0 :: int) \<le> size self"
  for self :: "'a t"
axiomatization where t'invariant'1:   "size self = len (data self)"
  for self :: "'a t"
axiomatization where t'invariant'2:   "\<forall>(x :: 'a). contents self x = numof (data self) x (0 :: int) (size self)"
  for self :: "'a t"
definition t'eq :: "'a t \<Rightarrow> 'a t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> size a = size b \<and> data a = data b \<and> contents a = contents b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t"
  and b :: "'a t"
theorem get'refn'vc:
  fixes i :: "int"
  fixes t1 :: "'a t"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < size t1"
  shows "(0 :: int) \<le> i"
  and "i < size t1"
  and "(0 :: int) < contents t1 (mixfix_lbrb (data t1) i)"
  sorry
end
