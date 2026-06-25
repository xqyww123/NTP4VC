theory my_bag_BagImpl_removeqtvc
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
theorem remove'vc:
  fixes i :: "int"
  fixes t1 :: "'a t"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < size t1"
  shows "let n :: int = size t1 - (1 :: int); o1 :: 'a rarray = data t1 in ((0 :: int) \<le> i \<and> i < len o1) \<and> (if i < n then ((0 :: int) \<le> n \<and> n < len (data t1)) \<and> ((0 :: int) \<le> i \<and> i < len (data t1)) \<and> (len (mixfix_lblsmnrb (data t1) i (mixfix_lbrb (data t1) n)) = len (data t1) \<longrightarrow> len (mixfix_lblsmnrb (data t1) i (mixfix_lbrb (data t1) n)) = len (data t1) \<longrightarrow> (0 :: int) \<le> n \<and> (\<forall>(t_data :: 'a rarray). len t_data = n \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < len (mixfix_lblsmnrb (data t1) i (mixfix_lbrb (data t1) n)) \<longrightarrow> i1 < n \<longrightarrow> mixfix_lbrb t_data i1 = mixfix_lbrb (mixfix_lblsmnrb (data t1) i (mixfix_lbrb (data t1) n)) i1) \<longrightarrow> (\<forall>(t2 :: 'a t). (((0 :: int) \<le> n \<and> n = len t_data) \<and> (\<forall>(x :: 'a). remove (mixfix_lbrb o1 i) (contents t1) x = numof t_data x (0 :: int) n)) \<and> (remove (mixfix_lbrb o1 i) (contents t1) = contents t2 \<and> t_data = data t2 \<and> n = size t2 \<longrightarrow> size t2 = size t1 - (1 :: int) \<and> infix_eqeq (contents t2) (remove (mixfix_lbrb (data t1) i) (contents t1)))))) else (0 :: int) \<le> n \<and> (\<forall>(t_data :: 'a rarray). len t_data = n \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < len (data t1) \<longrightarrow> i1 < n \<longrightarrow> mixfix_lbrb t_data i1 = mixfix_lbrb (data t1) i1) \<longrightarrow> (\<forall>(t2 :: 'a t). (((0 :: int) \<le> n \<and> n = len t_data) \<and> (\<forall>(x :: 'a). remove (mixfix_lbrb o1 i) (contents t1) x = numof t_data x (0 :: int) n)) \<and> (remove (mixfix_lbrb o1 i) (contents t1) = contents t2 \<and> t_data = data t2 \<and> n = size t2 \<longrightarrow> size t2 = size t1 - (1 :: int) \<and> infix_eqeq (contents t2) (remove (mixfix_lbrb (data t1) i) (contents t1))))))"
  sorry
end
