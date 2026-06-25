theory tables_Map_decompose_minqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing_def:   "(0 :: int) < int balancing"
typedecl  t
consts le :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "t"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "t"
  and y :: "t"
  and z :: "t"
consts eq :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where eq_def:   "eq x y \<longleftrightarrow> le x y \<and> le y x"
  for x :: "t"
  and y :: "t"
consts lt :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where lt_def:   "lt x y \<longleftrightarrow> le x y \<and> \<not>le y x"
  for x :: "t"
  and y :: "t"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "t"
  and y :: "t"
typedecl 'a t1
definition key :: "t \<times> 'a \<Rightarrow> t"
  where "key t2 = (case t2 of (a, _) \<Rightarrow> a)" for t2
typedecl  t2
axiomatization where assoc:   "True"
axiomatization where neutral'0:   "() = x"
  for x :: "unit"
axiomatization where neutral'1:   "x = ()"
  for x :: "unit"
typedecl  selector
definition selection_possible :: "'b \<Rightarrow> (t \<times> 'a) list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> lt (key (s ! nat i)) (key (s ! nat j)))" for x s
definition upper_bound_s :: "t \<Rightarrow> (t \<times> 'a) list \<Rightarrow> _"
  where "upper_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt (key (s ! nat i)) k)" for k s
definition lower_bound_s :: "t \<Rightarrow> (t \<times> 'a) list \<Rightarrow> _"
  where "lower_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt k (key (s ! nat i)))" for k s
definition selected :: "t \<Rightarrow> (t \<times> 'a) split \<Rightarrow> _"
  where "selected k e \<longleftrightarrow> upper_bound_s k (left1 e) \<and> lower_bound_s k (right1 e) \<and> (case middle e of (None :: (t \<times> 'a) option) \<Rightarrow> True | Some d \<Rightarrow> eq k (key d))" for k e
datatype 'a tree = Empty | Node "'a tree" "t \<times> 'a" "'a tree" "nat" "unit"
datatype 'a m = m'mk (seq: "(t \<times> 'a) list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> (t \<times> 'a) list"
  where "seq_model (Empty :: 'a tree) = ([] :: (t \<times> 'a) list)"
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
datatype 'a view = AEmpty | ANode "'a t3" "t \<times> 'a" "'a t3" "nat" "unit"
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
datatype 'a m2 = m'mk1 (domn: "t \<Rightarrow> bool") (func: "t \<Rightarrow> t \<times> 'a") (card: "int")
definition domain :: "(t \<times> 'a) list \<Rightarrow> t \<Rightarrow> _"
  where "domain s k \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length s)) \<and> eq (key (s ! nat i)) k)" for s k
consts make_func :: "(t \<times> 'a) list \<Rightarrow> t \<Rightarrow> t \<times> 'a"
axiomatization where make_func'spec:   "make_func s k = s ! nat i"
 if "selection_possible () s"
 and "domain s k"
 and "(0 :: int) \<le> i"
 and "i < int (length s)"
 and "eq (key (s ! nat i)) k"
  for s :: "(t \<times> 'a) list"
  and k :: "t"
  and i :: "int"
consts domain_closure :: "(t \<times> 'a) list \<Rightarrow> t \<Rightarrow> bool"
consts make_func_closure :: "(t \<times> 'a) list \<Rightarrow> t \<Rightarrow> t \<times> 'a"
axiomatization where domain_closure_def:   "domain_closure y y1 = True \<longleftrightarrow> domain y y1"
  for y :: "(t \<times> 'a) list"
  and y1 :: "t"
axiomatization where make_func_closure_def:   "make_func_closure y y1 = make_func y y1"
  for y :: "(t \<times> 'a) list"
  and y1 :: "t"
definition m3 :: "'a t4 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: (t \<Rightarrow> bool) \<Rightarrow> (t \<Rightarrow> t \<times> 'a) \<Rightarrow> int \<Rightarrow> 'a m2) (domain_closure (seq (m1 (field t5)))) (make_func_closure (seq (m1 (field t5)))) (int (length (seq (m1 (field t5)))))" for t5
datatype 'a view1 = AEmpty1 | ANode1 "'a t4" "t \<times> 'a" "'a t4" "nat"
typedecl 'a t5
datatype 'a m4 = m'mk2 (domn1: "t \<Rightarrow> bool") (func1: "t \<Rightarrow> 'a") (card1: "int")
consts fc :: "'a t4 \<Rightarrow> t \<Rightarrow> 'a"
axiomatization where fc_def:   "fc t6 k = (case func (m3 t6) k of (_, v) \<Rightarrow> v)"
  for t6 :: "'a t4"
  and k :: "t"
definition m5 :: "'a t4 \<Rightarrow> 'a m4"
  where "m5 t6 = m'mk2 (domn (m3 t6)) (fc t6) (card (m3 t6))" for t6
theorem decompose_min'vc:
  fixes result :: "((t \<times> 'a) \<times> 'a t4) option"
  fixes t6 :: "'a t4"
  assumes fact0: "case result of (None :: ((t \<times> 'a) \<times> 'a t4) option) \<Rightarrow> card (m3 t6) = (0 :: int) \<and> (\<forall>(k :: t). \<not>domn (m3 t6) k = True) | Some (d, r) \<Rightarrow> card (m3 t6) = card (m3 r) + (1 :: int) \<and> domn (m3 t6) (case d of (a, _) \<Rightarrow> a) = True \<and> func (m3 t6) (case d of (a, _) \<Rightarrow> a) = d \<and> \<not>domn (m3 r) (case d of (a, _) \<Rightarrow> a) = True \<and> (\<forall>(k :: t). lt k (case d of (a, _) \<Rightarrow> a) \<longrightarrow> \<not>domn (m3 t6) k = True) \<and> (\<forall>(k :: t). eq k (case d of (a, _) \<Rightarrow> a) \<longrightarrow> func (m3 t6) k = d) \<and> (\<forall>(k :: t). le k (case d of (a, _) \<Rightarrow> a) \<longrightarrow> \<not>domn (m3 r) k = True) \<and> (\<forall>(k :: t). lt (case d of (a, _) \<Rightarrow> a) k \<longrightarrow> domn (m3 r) k = True \<longleftrightarrow> domn (m3 t6) k = True) \<and> (\<forall>(k :: t). lt (case d of (a, _) \<Rightarrow> a) k \<and> domn (m3 r) k = True \<longrightarrow> func (m3 r) k = func (m3 t6) k)"
  shows "case result of (None :: ((t \<times> 'a) \<times> 'a t4) option) \<Rightarrow> card1 (m5 t6) = (0 :: int) \<and> (\<forall>(k :: t). \<not>domn1 (m5 t6) k = True) | Some ((k0, v), r) \<Rightarrow> card1 (m5 t6) = card1 (m5 r) + (1 :: int) \<and> domn1 (m5 t6) k0 = True \<and> func1 (m5 t6) k0 = v \<and> \<not>domn1 (m5 r) k0 = True \<and> (\<forall>(k :: t). lt k k0 \<longrightarrow> \<not>domn1 (m5 t6) k = True) \<and> (\<forall>(k :: t). eq k k0 \<longrightarrow> func1 (m5 t6) k = v) \<and> (\<forall>(k :: t). le k k0 \<longrightarrow> \<not>domn1 (m5 r) k = True) \<and> (\<forall>(k :: t). lt k0 k \<longrightarrow> domn1 (m5 r) k = True \<longleftrightarrow> domn1 (m5 t6) k = True) \<and> (\<forall>(k :: t). lt k0 k \<and> domn1 (m5 r) k = True \<longrightarrow> func1 (m5 r) k = func1 (m5 t6) k)"
  sorry
end
