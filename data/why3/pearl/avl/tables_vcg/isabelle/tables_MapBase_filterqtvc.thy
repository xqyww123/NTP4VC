theory tables_MapBase_filterqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing_def:   "(0 :: int) < int balancing"
typedecl 'a t
typedecl  t1
consts key :: "'a t \<Rightarrow> t1"
consts le :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "t1"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "t1"
  and y :: "t1"
  and z :: "t1"
consts eq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where eq_def:   "eq x y \<longleftrightarrow> le x y \<and> le y x"
  for x :: "t1"
  and y :: "t1"
consts lt :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where lt_def:   "lt x y \<longleftrightarrow> le x y \<and> \<not>le y x"
  for x :: "t1"
  and y :: "t1"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "t1"
  and y :: "t1"
typedecl  t2
axiomatization where assoc:   "True"
axiomatization where neutral'0:   "() = x"
  for x :: "unit"
axiomatization where neutral'1:   "x = ()"
  for x :: "unit"
typedecl  selector
definition selection_possible :: "'b \<Rightarrow> 'a t list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> lt (key (s ! nat i)) (key (s ! nat j)))" for x s
definition upper_bound_s :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "upper_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt (key (s ! nat i)) k)" for k s
definition lower_bound_s :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "lower_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt k (key (s ! nat i)))" for k s
definition selected :: "t1 \<Rightarrow> 'a t split \<Rightarrow> _"
  where "selected k e \<longleftrightarrow> upper_bound_s k (left1 e) \<and> lower_bound_s k (right1 e) \<and> (case middle e of (None :: 'a t option) \<Rightarrow> True | Some d \<Rightarrow> eq k (key d))" for k e
datatype 'a tree = Empty | Node "'a tree" "'a t" "'a tree" "nat" "unit"
datatype 'a m = m'mk (seq: "'a t list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> 'a t list"
  where "seq_model (Empty :: 'a tree) = ([] :: 'a t list)"
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
datatype 'a view = AEmpty | ANode "'a t3" "'a t" "'a t3" "nat" "unit"
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
datatype 'a m2 = m'mk1 (domn: "t1 \<Rightarrow> bool") (func: "t1 \<Rightarrow> 'a t") (card: "int")
definition domain :: "'a t list \<Rightarrow> t1 \<Rightarrow> _"
  where "domain s k \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length s)) \<and> eq (key (s ! nat i)) k)" for s k
consts make_func :: "'a t list \<Rightarrow> t1 \<Rightarrow> 'a t"
axiomatization where make_func'spec:   "make_func s k = s ! nat i"
 if "selection_possible () s"
 and "domain s k"
 and "(0 :: int) \<le> i"
 and "i < int (length s)"
 and "eq (key (s ! nat i)) k"
  for s :: "'a t list"
  and k :: "t1"
  and i :: "int"
consts domain_closure :: "'a t list \<Rightarrow> t1 \<Rightarrow> bool"
consts make_func_closure :: "'a t list \<Rightarrow> t1 \<Rightarrow> 'a t"
axiomatization where domain_closure_def:   "domain_closure y y1 = True \<longleftrightarrow> domain y y1"
  for y :: "'a t list"
  and y1 :: "t1"
axiomatization where make_func_closure_def:   "make_func_closure y y1 = make_func y y1"
  for y :: "'a t list"
  and y1 :: "t1"
definition m3 :: "'a t4 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: (t1 \<Rightarrow> bool) \<Rightarrow> (t1 \<Rightarrow> 'a t) \<Rightarrow> int \<Rightarrow> 'a m2) (domain_closure (seq (m1 (field t5)))) (make_func_closure (seq (m1 (field t5)))) (int (length (seq (m1 (field t5)))))" for t5
datatype 'a view1 = AEmpty1 | ANode1 "'a t4" "'a t" "'a t4" "nat"
theorem filter'vc:
  fixes o1 :: "'a view1"
  fixes a :: "'a t4"
  fixes p :: "'b t4"
  assumes fact0: "case o1 of (AEmpty1 :: 'a view1) \<Rightarrow> card (m3 a) = (0 :: int) \<and> (\<forall>(k :: t1). \<not>domn (m3 a) k = True) | ANode1 l d r h \<Rightarrow> card (m3 a) = (1 :: int) + card (m3 l) + card (m3 r) \<and> int h = hgt (m1 (field a)) \<and> (let k0 :: t1 = key d in (\<forall>(k :: t1). lt k k0 \<longrightarrow> domn (m3 l) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt k k0 \<and> domn (m3 l) k = True \<longrightarrow> func (m3 l) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le k0 k \<longrightarrow> \<not>domn (m3 l) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<longrightarrow> domn (m3 r) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<and> domn (m3 r) k = True \<longrightarrow> func (m3 r) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le k k0 \<longrightarrow> \<not>domn (m3 r) k = True) \<and> (\<forall>(k :: t1). eq k k0 \<longrightarrow> domn (m3 a) k = True \<and> func (m3 a) k = d) \<and> domn (m3 a) k0 = True \<and> func (m3 a) k0 = d)"
  shows "case o1 of (AEmpty1 :: 'a view1) \<Rightarrow> True | ANode1 al ad ar ah \<Rightarrow> (\<forall>(o2 :: 'b view1). (case o2 of (AEmpty1 :: 'b view1) \<Rightarrow> card (m3 p) = (0 :: int) \<and> (\<forall>(k :: t1). \<not>domn (m3 p) k = True) | ANode1 l d r h \<Rightarrow> card (m3 p) = (1 :: int) + card (m3 l) + card (m3 r) \<and> int h = hgt (m1 (field p)) \<and> (let k0 :: t1 = key d in (\<forall>(k :: t1). lt k k0 \<longrightarrow> domn (m3 l) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k k0 \<and> domn (m3 l) k = True \<longrightarrow> func (m3 l) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k0 k \<longrightarrow> \<not>domn (m3 l) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<longrightarrow> domn (m3 r) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<and> domn (m3 r) k = True \<longrightarrow> func (m3 r) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k k0 \<longrightarrow> \<not>domn (m3 r) k = True) \<and> (\<forall>(k :: t1). eq k k0 \<longrightarrow> domn (m3 p) k = True \<and> func (m3 p) k = d) \<and> domn (m3 p) k0 = True \<and> func (m3 p) k0 = d)) \<longrightarrow> (case o2 of (AEmpty1 :: 'b view1) \<Rightarrow> True | ANode1 pl pd pr ph \<Rightarrow> (if ah \<le> ph then let o3 :: t1 = key pd in \<forall>(al1 :: 'a t4) (ad1 :: 'a t option) (ar1 :: 'a t4). (\<forall>(k :: t1). lt k o3 \<longrightarrow> domn (m3 al1) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt k o3 \<and> domn (m3 al1) k = True \<longrightarrow> func (m3 al1) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le o3 k \<longrightarrow> \<not>domn (m3 al1) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<longrightarrow> domn (m3 ar1) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<and> domn (m3 ar1) k = True \<longrightarrow> func (m3 ar1) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le k o3 \<longrightarrow> \<not>domn (m3 ar1) k = True) \<and> (case ad1 of (None :: 'a t option) \<Rightarrow> card (m3 a) = card (m3 al1) + card (m3 ar1) \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> \<not>domn (m3 a) k = True) \<and> \<not>domn (m3 a) o3 = True | Some d \<Rightarrow> card (m3 a) = card (m3 al1) + card (m3 ar1) + (1 :: int) \<and> eq (key d) o3 \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> domn (m3 a) k = True \<and> func (m3 a) k = d) \<and> domn (m3 a) o3 = True \<and> func (m3 a) o3 = d) \<longrightarrow> ((0 :: int) \<le> card (m3 a) + card (m3 p) \<and> card (m3 al1) + card (m3 pl) < card (m3 a) + card (m3 p)) \<and> (\<forall>(fl :: 'a t4). (\<forall>(k :: t1). domn (m3 fl) k = True \<longleftrightarrow> domn (m3 al1) k = True \<and> domn (m3 pl) k = True) \<and> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> func (m3 fl) k = func (m3 al1) k) \<and> card (m3 fl) \<le> card (m3 al1) \<and> card (m3 fl) \<le> card (m3 pl) \<longrightarrow> ((0 :: int) \<le> card (m3 a) + card (m3 p) \<and> card (m3 ar1) + card (m3 pr) < card (m3 a) + card (m3 p)) \<and> (\<forall>(fr :: 'a t4). (\<forall>(k :: t1). domn (m3 fr) k = True \<longleftrightarrow> domn (m3 ar1) k = True \<and> domn (m3 pr) k = True) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> func (m3 fr) k = func (m3 ar1) k) \<and> card (m3 fr) \<le> card (m3 ar1) \<and> card (m3 fr) \<le> card (m3 pr) \<longrightarrow> (case ad1 of (None :: 'a t option) \<Rightarrow> (\<forall>(k1 :: t1) (k2 :: t1). domn (m3 fl) k1 = True \<and> domn (m3 fr) k2 = True \<longrightarrow> lt k1 k2) | Some ad2 \<Rightarrow> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> lt k (key ad2)) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> lt (key ad2) k)))) else let o3 :: t1 = key ad in \<forall>(pl1 :: 'b t4) (pd1 :: 'b t option) (pr1 :: 'b t4). (\<forall>(k :: t1). lt k o3 \<longrightarrow> domn (m3 pl1) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k o3 \<and> domn (m3 pl1) k = True \<longrightarrow> func (m3 pl1) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le o3 k \<longrightarrow> \<not>domn (m3 pl1) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<longrightarrow> domn (m3 pr1) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<and> domn (m3 pr1) k = True \<longrightarrow> func (m3 pr1) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k o3 \<longrightarrow> \<not>domn (m3 pr1) k = True) \<and> (case pd1 of (None :: 'b t option) \<Rightarrow> card (m3 p) = card (m3 pl1) + card (m3 pr1) \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> \<not>domn (m3 p) k = True) \<and> \<not>domn (m3 p) o3 = True | Some d \<Rightarrow> card (m3 p) = card (m3 pl1) + card (m3 pr1) + (1 :: int) \<and> eq (key d) o3 \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> domn (m3 p) k = True \<and> func (m3 p) k = d) \<and> domn (m3 p) o3 = True \<and> func (m3 p) o3 = d) \<longrightarrow> ((0 :: int) \<le> card (m3 a) + card (m3 p) \<and> card (m3 al) + card (m3 pl1) < card (m3 a) + card (m3 p)) \<and> (\<forall>(fl :: 'a t4). (\<forall>(k :: t1). domn (m3 fl) k = True \<longleftrightarrow> domn (m3 al) k = True \<and> domn (m3 pl1) k = True) \<and> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> func (m3 fl) k = func (m3 al) k) \<and> card (m3 fl) \<le> card (m3 al) \<and> card (m3 fl) \<le> card (m3 pl1) \<longrightarrow> ((0 :: int) \<le> card (m3 a) + card (m3 p) \<and> card (m3 ar) + card (m3 pr1) < card (m3 a) + card (m3 p)) \<and> (\<forall>(fr :: 'a t4). (\<forall>(k :: t1). domn (m3 fr) k = True \<longleftrightarrow> domn (m3 ar) k = True \<and> domn (m3 pr1) k = True) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> func (m3 fr) k = func (m3 ar) k) \<and> card (m3 fr) \<le> card (m3 ar) \<and> card (m3 fr) \<le> card (m3 pr1) \<longrightarrow> (case pd1 of (None :: 'b t option) \<Rightarrow> (\<forall>(k1 :: t1) (k2 :: t1). domn (m3 fl) k1 = True \<and> domn (m3 fr) k2 = True \<longrightarrow> lt k1 k2) | _ \<Rightarrow> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> lt k (key ad)) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> lt (key ad) k)))))))"
  and "\<forall>(result :: 'a t4). (case o1 of (AEmpty1 :: 'a view1) \<Rightarrow> result = a | ANode1 al ad ar ah \<Rightarrow> (\<exists>(o2 :: 'b view1). (case o2 of (AEmpty1 :: 'b view1) \<Rightarrow> card (m3 p) = (0 :: int) \<and> (\<forall>(k :: t1). \<not>domn (m3 p) k = True) | ANode1 l d r h \<Rightarrow> card (m3 p) = (1 :: int) + card (m3 l) + card (m3 r) \<and> int h = hgt (m1 (field p)) \<and> (let k0 :: t1 = key d in (\<forall>(k :: t1). lt k k0 \<longrightarrow> domn (m3 l) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k k0 \<and> domn (m3 l) k = True \<longrightarrow> func (m3 l) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k0 k \<longrightarrow> \<not>domn (m3 l) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<longrightarrow> domn (m3 r) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k0 k \<and> domn (m3 r) k = True \<longrightarrow> func (m3 r) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k k0 \<longrightarrow> \<not>domn (m3 r) k = True) \<and> (\<forall>(k :: t1). eq k k0 \<longrightarrow> domn (m3 p) k = True \<and> func (m3 p) k = d) \<and> domn (m3 p) k0 = True \<and> func (m3 p) k0 = d)) \<and> (case o2 of (AEmpty1 :: 'b view1) \<Rightarrow> card (m3 result) = (0 :: int) \<and> (\<forall>(k :: t1). \<not>domn (m3 result) k = True) | ANode1 pl pd pr ph \<Rightarrow> (if ah \<le> ph then let o3 :: t1 = key pd in \<exists>(lf :: 'a t4) (o4 :: 'a t option) (rg :: 'a t4). ((\<forall>(k :: t1). lt k o3 \<longrightarrow> domn (m3 lf) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt k o3 \<and> domn (m3 lf) k = True \<longrightarrow> func (m3 lf) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le o3 k \<longrightarrow> \<not>domn (m3 lf) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<longrightarrow> domn (m3 rg) k = True \<longleftrightarrow> domn (m3 a) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<and> domn (m3 rg) k = True \<longrightarrow> func (m3 rg) k = func (m3 a) k) \<and> (\<forall>(k :: t1). le k o3 \<longrightarrow> \<not>domn (m3 rg) k = True) \<and> (case o4 of (None :: 'a t option) \<Rightarrow> card (m3 a) = card (m3 lf) + card (m3 rg) \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> \<not>domn (m3 a) k = True) \<and> \<not>domn (m3 a) o3 = True | Some d \<Rightarrow> card (m3 a) = card (m3 lf) + card (m3 rg) + (1 :: int) \<and> eq (key d) o3 \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> domn (m3 a) k = True \<and> func (m3 a) k = d) \<and> domn (m3 a) o3 = True \<and> func (m3 a) o3 = d)) \<and> (\<exists>(fl :: 'a t4). ((\<forall>(k :: t1). domn (m3 fl) k = True \<longleftrightarrow> domn (m3 lf) k = True \<and> domn (m3 pl) k = True) \<and> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> func (m3 fl) k = func (m3 lf) k) \<and> card (m3 fl) \<le> card (m3 lf) \<and> card (m3 fl) \<le> card (m3 pl)) \<and> (\<exists>(fr :: 'a t4). ((\<forall>(k :: t1). domn (m3 fr) k = True \<longleftrightarrow> domn (m3 rg) k = True \<and> domn (m3 pr) k = True) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> func (m3 fr) k = func (m3 rg) k) \<and> card (m3 fr) \<le> card (m3 rg) \<and> card (m3 fr) \<le> card (m3 pr)) \<and> (case o4 of (None :: 'a t option) \<Rightarrow> (\<forall>(k :: t1). domn (m3 result) k = True \<longleftrightarrow> domn (m3 fl) k = True \<or> domn (m3 fr) k = True) \<and> (\<forall>(k :: t1). domn (m3 result) k = True \<and> domn (m3 fl) k = True \<longrightarrow> func (m3 result) k = func (m3 fl) k) \<and> (\<forall>(k :: t1). domn (m3 result) k = True \<and> domn (m3 fr) k = True \<longrightarrow> func (m3 result) k = func (m3 fr) k) \<and> card (m3 result) = card (m3 fl) + card (m3 fr) | Some ad1 \<Rightarrow> (\<forall>(k :: t1). lt k (key ad1) \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 fl) k = True) \<and> (\<forall>(k :: t1). lt k (key ad1) \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 fl) k) \<and> (\<forall>(k :: t1). lt (key ad1) k \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 fr) k = True) \<and> (\<forall>(k :: t1). lt (key ad1) k \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 fr) k) \<and> (\<forall>(k :: t1). eq k (key ad1) \<longrightarrow> domn (m3 result) k = True \<and> func (m3 result) k = ad1) \<and> card (m3 result) = (1 :: int) + card (m3 fl) + card (m3 fr)))) else let o3 :: t1 = key ad in \<exists>(lf :: 'b t4) (o4 :: 'b t option) (rg :: 'b t4). ((\<forall>(k :: t1). lt k o3 \<longrightarrow> domn (m3 lf) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt k o3 \<and> domn (m3 lf) k = True \<longrightarrow> func (m3 lf) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le o3 k \<longrightarrow> \<not>domn (m3 lf) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<longrightarrow> domn (m3 rg) k = True \<longleftrightarrow> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). lt o3 k \<and> domn (m3 rg) k = True \<longrightarrow> func (m3 rg) k = func (m3 p) k) \<and> (\<forall>(k :: t1). le k o3 \<longrightarrow> \<not>domn (m3 rg) k = True) \<and> (case o4 of (None :: 'b t option) \<Rightarrow> card (m3 p) = card (m3 lf) + card (m3 rg) \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> \<not>domn (m3 p) k = True) \<and> \<not>domn (m3 p) o3 = True | Some d \<Rightarrow> card (m3 p) = card (m3 lf) + card (m3 rg) + (1 :: int) \<and> eq (key d) o3 \<and> (\<forall>(k :: t1). eq k o3 \<longrightarrow> domn (m3 p) k = True \<and> func (m3 p) k = d) \<and> domn (m3 p) o3 = True \<and> func (m3 p) o3 = d)) \<and> (\<exists>(fl :: 'a t4). ((\<forall>(k :: t1). domn (m3 fl) k = True \<longleftrightarrow> domn (m3 al) k = True \<and> domn (m3 lf) k = True) \<and> (\<forall>(k :: t1). domn (m3 fl) k = True \<longrightarrow> func (m3 fl) k = func (m3 al) k) \<and> card (m3 fl) \<le> card (m3 al) \<and> card (m3 fl) \<le> card (m3 lf)) \<and> (\<exists>(fr :: 'a t4). ((\<forall>(k :: t1). domn (m3 fr) k = True \<longleftrightarrow> domn (m3 ar) k = True \<and> domn (m3 rg) k = True) \<and> (\<forall>(k :: t1). domn (m3 fr) k = True \<longrightarrow> func (m3 fr) k = func (m3 ar) k) \<and> card (m3 fr) \<le> card (m3 ar) \<and> card (m3 fr) \<le> card (m3 rg)) \<and> (case o4 of (None :: 'b t option) \<Rightarrow> (\<forall>(k :: t1). domn (m3 result) k = True \<longleftrightarrow> domn (m3 fl) k = True \<or> domn (m3 fr) k = True) \<and> (\<forall>(k :: t1). domn (m3 result) k = True \<and> domn (m3 fl) k = True \<longrightarrow> func (m3 result) k = func (m3 fl) k) \<and> (\<forall>(k :: t1). domn (m3 result) k = True \<and> domn (m3 fr) k = True \<longrightarrow> func (m3 result) k = func (m3 fr) k) \<and> card (m3 result) = card (m3 fl) + card (m3 fr) | _ \<Rightarrow> (\<forall>(k :: t1). lt k (key ad) \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 fl) k = True) \<and> (\<forall>(k :: t1). lt k (key ad) \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 fl) k) \<and> (\<forall>(k :: t1). lt (key ad) k \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 fr) k = True) \<and> (\<forall>(k :: t1). lt (key ad) k \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 fr) k) \<and> (\<forall>(k :: t1). eq k (key ad) \<longrightarrow> domn (m3 result) k = True \<and> func (m3 result) k = ad) \<and> card (m3 result) = (1 :: int) + card (m3 fl) + card (m3 fr)))))))) \<longrightarrow> (\<forall>(k :: t1). domn (m3 result) k = True \<longleftrightarrow> domn (m3 a) k = True \<and> domn (m3 p) k = True) \<and> (\<forall>(k :: t1). domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 a) k) \<and> card (m3 result) \<le> card (m3 a) \<and> card (m3 result) \<le> card (m3 p)"
  sorry
end
