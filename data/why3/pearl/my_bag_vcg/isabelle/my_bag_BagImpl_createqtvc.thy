theory my_bag_BagImpl_createqtvc
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
consts fc1 :: "'a \<Rightarrow> int"
consts fc2 :: "'a \<Rightarrow> int"
axiomatization where fc1_def:   "fc1 y0 = (0 :: int)"
  for y0 :: "'a"
axiomatization where fc2_def:   "fc2 y0 = (0 :: int)"
  for y0 :: "'a"
theorem create'vc:
  fixes dummy :: "'a"
  shows "let o1 :: 'a \<Rightarrow> int = fc1 in (0 :: int) \<le> (0 :: int) \<and> (\<forall>(o2 :: 'a rarray). len o2 = (0 :: int) \<and> my_bag_ResizableArraySpec.data o2 = (const :: 'a \<Rightarrow> int \<Rightarrow> 'a) dummy \<longrightarrow> (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) = len o2) \<and> (\<forall>(x :: 'a). o1 x = numof o2 x (0 :: int) (0 :: int))) \<and> (\<forall>(result :: 'a t). size result = (0 :: int) \<and> data result = o2 \<and> contents result = o1 \<longrightarrow> size result = (0 :: int) \<and> infix_eqeq (contents result) fc2))"
  sorry
end
