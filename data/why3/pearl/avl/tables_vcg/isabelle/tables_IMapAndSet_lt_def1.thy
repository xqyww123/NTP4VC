theory tables_IMapAndSet_lt_def1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
typedecl  t
consts balancing :: "nat"
axiomatization where balancing_def:   "int balancing = int (0 :: nat) + (1 :: int)"
typedecl 'a t1
definition key :: "int \<times> 'a \<Rightarrow> int"
  where "key t2 = (case t2 of (a, _) \<Rightarrow> a)" for t2
typedecl  t2
axiomatization where assoc:   "True"
axiomatization where neutral'0:   "() = x"
  for x :: "unit"
axiomatization where neutral'1:   "x = ()"
  for x :: "unit"
typedecl  selector
definition selection_possible :: "'b \<Rightarrow> (int \<times> 'a) list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> key (s ! nat i) < key (s ! nat j))" for x s
definition upper_bound_s :: "int \<Rightarrow> (int \<times> 'a) list \<Rightarrow> _"
  where "upper_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> key (s ! nat i) < k)" for k s
definition lower_bound_s :: "int \<Rightarrow> (int \<times> 'a) list \<Rightarrow> _"
  where "lower_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> k < key (s ! nat i))" for k s
definition selected :: "int \<Rightarrow> (int \<times> 'a) split \<Rightarrow> _"
  where "selected k e \<longleftrightarrow> upper_bound_s k (left1 e) \<and> lower_bound_s k (right1 e) \<and> (case middle e of (None :: (int \<times> 'a) option) \<Rightarrow> True | Some d \<Rightarrow> k = key d)" for k e
datatype 'a tree = Empty | Node "'a tree" "int \<times> 'a" "'a tree" "nat" "unit"
datatype 'a m = m'mk (seq: "(int \<times> 'a) list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> (int \<times> 'a) list"
  where "seq_model (Empty :: 'a tree) = ([] :: (int \<times> 'a) list)"
      | "seq_model (Node l d r x x0) = node_model (seq_model l) d (seq_model r)" for l d r x x0
fun real_height :: "'a tree \<Rightarrow> int"
  where "real_height (Empty :: 'a tree) = (0 :: int)"
      | "real_height (Node l x r x0 x1) = (let hl :: int = real_height l; hr :: int = real_height r in (1 :: int) + (if hl < hr then hr else hl))" for l x r x0 x1
fun balanced :: "'a tree \<Rightarrow> _"
  where "balanced (Empty :: 'a tree) = True"
      | "balanced (Node l x r h m1) = (int h = real_height (Node l x r h m1) \<and> m1 = () \<and> (-int balancing \<le> real_height r - real_height l \<and> real_height r - real_height l \<le> int balancing) \<and> balanced l \<and> balanced r)" for l x r h m1
typedecl 'a t3
consts repr :: "'a t3 \<Rightarrow> 'a tree"
consts m1 :: "'a t3 \<Rightarrow> 'a m"
axiomatization where t'invariant'0:   "balanced (repr self)"
  for self :: "'a t3"
axiomatization where t'invariant'1:   "seq (m1 self) = seq_model (repr self)"
  for self :: "'a t3"
axiomatization where t'invariant'2:   "hgt (m1 self) = real_height (repr self)"
  for self :: "'a t3"
definition t'eq :: "'a t3 \<Rightarrow> 'a t3 \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> repr a = repr b \<and> m1 a = m1 b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t3"
  and b :: "'a t3"
datatype 'a view = AEmpty | ANode "'a t3" "int \<times> 'a" "'a t3" "nat" "unit"
typedecl  part
typedecl 'a t4
consts field :: "'a t4 \<Rightarrow> 'a t3"
axiomatization where t'invariant1:   "selection_possible () (seq (m1 (field self)))"
  for self :: "'a t4"
definition t'eq1 :: "'a t4 \<Rightarrow> 'a t4 \<Rightarrow> _"
  where "t'eq1 a b \<longleftrightarrow> field a = field b" for a b
axiomatization where t'inj1:   "a = b"
 if "t'eq1 a b"
  for a :: "'a t4"
  and b :: "'a t4"
datatype 'a m2 = m'mk1 (domn: "int \<Rightarrow> bool") (func: "int \<Rightarrow> int \<times> 'a") (card: "int")
definition domain :: "(int \<times> 'a) list \<Rightarrow> int \<Rightarrow> _"
  where "domain s k \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length s)) \<and> key (s ! nat i) = k)" for s k
consts make_func :: "(int \<times> 'a) list \<Rightarrow> int \<Rightarrow> int \<times> 'a"
axiomatization where make_func'spec:   "make_func s k = s ! nat i"
 if "selection_possible () s"
 and "domain s k"
 and "(0 :: int) \<le> i"
 and "i < int (length s)"
 and "key (s ! nat i) = k"
  for s :: "(int \<times> 'a) list"
  and k :: "int"
  and i :: "int"
consts domain_closure :: "(int \<times> 'a) list \<Rightarrow> int \<Rightarrow> bool"
consts make_func_closure :: "(int \<times> 'a) list \<Rightarrow> int \<Rightarrow> int \<times> 'a"
axiomatization where domain_closure_def:   "domain_closure y y1 = True \<longleftrightarrow> domain y y1"
  for y :: "(int \<times> 'a) list"
  and y1 :: "int"
axiomatization where make_func_closure_def:   "make_func_closure y y1 = make_func y y1"
  for y :: "(int \<times> 'a) list"
  and y1 :: "int"
definition m3 :: "'a t4 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: (int \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> int \<times> 'a) \<Rightarrow> int \<Rightarrow> 'a m2) (domain_closure (seq (m1 (field t5)))) (make_func_closure (seq (m1 (field t5)))) (int (length (seq (m1 (field t5)))))" for t5
datatype 'a view1 = AEmpty1 | ANode1 "'a t4" "int \<times> 'a" "'a t4" "nat"
typedecl 'a t5
datatype 'a m4 = m'mk2 (domn1: "int \<Rightarrow> bool") (func1: "int \<Rightarrow> 'a") (card1: "int")
consts fc :: "'a t4 \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where fc_def:   "fc t6 k = (case func (m3 t6) k of (_, v) \<Rightarrow> v)"
  for t6 :: "'a t4"
  and k :: "int"
definition m5 :: "'a t4 \<Rightarrow> 'a m4"
  where "m5 t6 = m'mk2 (domn (m3 t6)) (fc t6) (card (m3 t6))" for t6
theorem lt_def:
  fixes x :: "int"
  fixes y :: "int"
  shows "x < y \<longleftrightarrow> x \<le> y \<and> \<not>y \<le> x"
  sorry
end
