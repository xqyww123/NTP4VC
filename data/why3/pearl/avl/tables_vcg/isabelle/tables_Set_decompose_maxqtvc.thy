theory tables_Set_decompose_maxqtvc
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
typedecl  t2
axiomatization where assoc:   "True"
axiomatization where neutral'0:   "() = x"
  for x :: "unit"
axiomatization where neutral'1:   "x = ()"
  for x :: "unit"
typedecl  selector
definition selection_possible :: "'b \<Rightarrow> t list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> lt (s ! nat i) (s ! nat j))" for x s
definition upper_bound_s :: "t \<Rightarrow> t list \<Rightarrow> _"
  where "upper_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt (s ! nat i) k)" for k s
definition lower_bound_s :: "t \<Rightarrow> t list \<Rightarrow> _"
  where "lower_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt k (s ! nat i))" for k s
definition selected :: "t \<Rightarrow> t split \<Rightarrow> _"
  where "selected k e \<longleftrightarrow> upper_bound_s k (left1 e) \<and> lower_bound_s k (right1 e) \<and> (case middle e of None \<Rightarrow> True | Some d \<Rightarrow> eq k d)" for k e
datatype 'a tree = Empty | Node "'a tree" "t" "'a tree" "nat" "unit"
datatype 'a m = m'mk (seq: "t list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> t list"
  where "seq_model (Empty :: 'a tree) = []"
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
datatype 'a view = AEmpty | ANode "'a t3" "t" "'a t3" "nat" "unit"
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
datatype 'a m2 = m'mk1 (domn: "t \<Rightarrow> bool") (func: "t \<Rightarrow> t") (card: "int")
definition domain :: "t list \<Rightarrow> t \<Rightarrow> _"
  where "domain s k \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length s)) \<and> eq (s ! nat i) k)" for s k
consts make_func :: "t list \<Rightarrow> t \<Rightarrow> t"
axiomatization where make_func'spec:   "make_func s k = s ! nat i"
 if "selection_possible () s"
 and "domain s k"
 and "(0 :: int) \<le> i"
 and "i < int (length s)"
 and "eq (s ! nat i) k"
  for s :: "t list"
  and k :: "t"
  and i :: "int"
consts domain_closure :: "t list \<Rightarrow> t \<Rightarrow> bool"
consts make_func_closure :: "t list \<Rightarrow> t \<Rightarrow> t"
axiomatization where domain_closure_def:   "domain_closure y y1 = True \<longleftrightarrow> domain y y1"
  for y :: "t list"
  and y1 :: "t"
axiomatization where make_func_closure_def:   "make_func_closure y y1 = make_func y y1"
  for y :: "t list"
  and y1 :: "t"
definition m3 :: "'a t4 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: (t \<Rightarrow> bool) \<Rightarrow> (t \<Rightarrow> t) \<Rightarrow> int \<Rightarrow> 'a m2) (domain_closure (seq (m1 (field t5)))) (make_func_closure (seq (m1 (field t5)))) (int (length (seq (m1 (field t5)))))" for t5
datatype 'a view1 = AEmpty1 | ANode1 "'a t4" "t" "'a t4" "nat"
typedecl  t5
theorem decompose_max'vc:
  fixes result :: "(unit t4 \<times> t) option"
  fixes t6 :: "unit t4"
  assumes fact0: "case result of None \<Rightarrow> card (m3 t6) = (0 :: int) \<and> (\<forall>(k :: t). \<not>domn (m3 t6) k = True) | Some (l, d) \<Rightarrow> card (m3 t6) = card (m3 l) + (1 :: int) \<and> domn (m3 t6) d = True \<and> func (m3 t6) d = d \<and> \<not>domn (m3 l) d = True \<and> (\<forall>(k :: t). lt d k \<longrightarrow> \<not>domn (m3 t6) k = True) \<and> (\<forall>(k :: t). eq k d \<longrightarrow> func (m3 t6) k = d) \<and> (\<forall>(k :: t). le d k \<longrightarrow> \<not>domn (m3 l) k = True) \<and> (\<forall>(k :: t). lt k d \<longrightarrow> domn (m3 l) k = True \<longleftrightarrow> domn (m3 t6) k = True) \<and> (\<forall>(k :: t). lt k d \<and> domn (m3 l) k = True \<longrightarrow> func (m3 l) k = func (m3 t6) k)"
  shows "case result of None \<Rightarrow> card (m3 t6) = (0 :: int) \<and> (\<forall>(k :: t). \<not>domn (m3 t6) k = True) | Some (l, k0) \<Rightarrow> card (m3 t6) = card (m3 l) + (1 :: int) \<and> domn (m3 t6) k0 = True \<and> \<not>domn (m3 l) k0 = True \<and> (\<forall>(k :: t). lt k0 k \<longrightarrow> \<not>domn (m3 t6) k = True) \<and> (\<forall>(k :: t). le k0 k \<longrightarrow> \<not>domn (m3 l) k = True) \<and> (\<forall>(k :: t). lt k0 k \<longrightarrow> domn (m3 l) k = True \<longleftrightarrow> domn (m3 t6) k = True)"
  sorry
end
