theory my_bag_BagImpl_addqtvc
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
theorem add'vc:
  fixes t1 :: "'a t"
  fixes x :: "'a"
  shows "let n :: int = size t1; o1 :: int = n + (1 :: int) in (0 :: int) \<le> o1 \<and> (\<forall>(t_data :: 'a rarray). len t_data = o1 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < len (data t1) \<longrightarrow> i < o1 \<longrightarrow> mixfix_lbrb t_data i = mixfix_lbrb (data t1) i) \<longrightarrow> ((0 :: int) \<le> n \<and> n < len t_data) \<and> (len (mixfix_lblsmnrb t_data n x) = len t_data \<longrightarrow> len (mixfix_lblsmnrb t_data n x) = len t_data \<longrightarrow> (\<forall>(t2 :: 'a t). (((0 :: int) \<le> n + (1 :: int) \<and> n + (1 :: int) = len (mixfix_lblsmnrb t_data n x)) \<and> (\<forall>(x1 :: 'a). add x (contents t1) x1 = numof (mixfix_lblsmnrb t_data n x) x1 (0 :: int) (n + (1 :: int)))) \<and> (add x (contents t1) = contents t2 \<and> mixfix_lblsmnrb t_data n x = data t2 \<and> n + (1 :: int) = size t2 \<longrightarrow> size t2 = size t1 + (1 :: int) \<and> infix_eqeq (contents t2) (add x (contents t1))))))"
  sorry
end
