theory my_bag_BagImpl_clearqtvc
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
theorem clear'vc:
  fixes t1 :: "'a t"
  shows "let o1 :: 'a rarray = data t1 in (0 :: int) \<le> (0 :: int) \<and> (\<forall>(t_data :: 'a rarray). len t_data = (0 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < len o1 \<longrightarrow> i < (0 :: int) \<longrightarrow> mixfix_lbrb t_data i = mixfix_lbrb o1 i) \<longrightarrow> (\<forall>(t2 :: 'a t) (t_contents :: 'a \<Rightarrow> int). (\<forall>(y0 :: 'a). t_contents y0 = (0 :: int)) \<longrightarrow> (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) = len t_data) \<and> (\<forall>(x :: 'a). t_contents x = numof t_data x (0 :: int) (0 :: int))) \<and> (t_contents = contents t2 \<and> t_data = data t2 \<and> (0 :: int) = size t2 \<longrightarrow> size t2 = (0 :: int) \<and> infix_eqeq (contents t2) fc2)))"
  sorry
end
