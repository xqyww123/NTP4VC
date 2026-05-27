theory ral_RAL_harnessqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl  m
typedecl  t
axiomatization where assoc:   "a + (b + c) = a + b + c"
  for a :: "int"
  and b :: "int"
  and c :: "int"
axiomatization where neutral'0:   "x + (0 :: int) = x"
  for x :: "int"
axiomatization where neutral'1:   "x = (0 :: int) + x"
  for x :: "int"
consts agg :: "('a \<Rightarrow> int) \<Rightarrow> 'a list \<Rightarrow> int"
axiomatization where agg'def:   "if int (length s) = (0 :: int) then agg f s = (0 :: int) else agg f s = f (s ! (0 :: nat)) + agg f (drop (1 :: nat) s)"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> int"
typedecl 'a t1
definition measure :: "'a \<Rightarrow> int"
  where "measure x = (1 :: int)" for x
datatype  selector = selector'mk (index: "int") (hole: "bool")
definition selection_possible :: "selector \<Rightarrow> 'a list \<Rightarrow> _"
  where "selection_possible s l \<longleftrightarrow> (0 :: int) \<le> index s \<and> (if hole s = True then index s \<le> int (length l) else index s < int (length l))" for s l
definition selected :: "selector \<Rightarrow> 'a split \<Rightarrow> _"
  where "selected s e \<longleftrightarrow> index s = int (length (left1 e)) \<and> (hole s = True \<longleftrightarrow> middle e = (None :: 'a option))" for s e
datatype 'a tree = Empty | Node "'a tree" "'a" "'a tree" "nat" "int"
datatype 'a m1 = m'mk (seq: "'a list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> 'a list"
  where "seq_model (Empty :: 'a tree) = ([] :: 'a list)"
      | "seq_model (Node l d r x x0) = node_model (seq_model l) d (seq_model r)" for l d r x x0
fun real_height :: "'a tree \<Rightarrow> int"
  where "real_height (Empty :: 'a tree) = (0 :: int)"
      | "real_height (Node l x r x0 x1) = (let hl :: int = real_height l; hr :: int = real_height r in (1 :: int) + (if hl < hr then hr else hl))" for l x r x0 x1
consts measure_closure :: "'a \<Rightarrow> int"
axiomatization where measure_closure_def:   "measure_closure y = measure y"
  for y :: "'a"
fun balanced :: "'a tree \<Rightarrow> _"
  where "balanced (Empty :: 'a tree) = True"
      | "balanced (Node l x r h m2) = (int h = real_height (Node l x r h m2) \<and> m2 = agg measure_closure (seq_model (Node l x r h m2)) \<and> (-int balancing \<le> real_height r - real_height l \<and> real_height r - real_height l \<le> int balancing) \<and> balanced l \<and> balanced r)" for l x r h m2
typedecl 'a t2
consts repr :: "'a t2 \<Rightarrow> 'a tree"
consts m2 :: "'a t2 \<Rightarrow> 'a m1"
axiomatization where t'invariant'0:   "balanced (repr self)"
  for self :: "'a t2"
axiomatization where t'invariant'1:   "seq (m2 self) = seq_model (repr self)"
  for self :: "'a t2"
axiomatization where t'invariant'2:   "hgt (m2 self) = real_height (repr self)"
  for self :: "'a t2"
definition t'eq :: "'a t2 \<Rightarrow> 'a t2 \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> repr a = repr b \<and> m2 a = m2 b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t2"
  and b :: "'a t2"
datatype 'a view = AEmpty | ANode "'a t2" "'a" "'a t2" "nat" "int"
typedecl  part
typedecl 'a t3
typedecl 'a m3
theorem harness'vc:
  fixes a :: "int t2"
  fixes b :: "int t2"
  assumes fact0: "(43 :: int) < int (length (seq (m2 a)))"
  assumes fact1: "(43 :: int) < int (length (seq (m2 b)))"
  assumes fact2: "\<forall>(n :: int). (0 :: int) \<le> n \<and> n < int (length (seq (m2 a))) \<longrightarrow> seq (m2 a) ! nat n = (0 :: int)"
  assumes fact3: "\<forall>(n :: int). (0 :: int) \<le> n \<and> n < int (length (seq (m2 b))) \<longrightarrow> seq (m2 b) ! nat n = (1 :: int)"
  shows "(0 :: int) \<le> (1 :: int)"
  and "(1 :: int) < int (length (seq (m2 a)))"
  and "\<forall>(a1 :: int t2). seq (m2 a1) = (seq (m2 a))[nat (1 :: int) := 1 :: int] \<and> length (seq (m2 a1)) = length (seq (m2 a)) \<and> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < int (length (seq (m2 a)))) \<and> \<not>i = (1 :: int) \<longrightarrow> seq (m2 a1) ! nat i = seq (m2 a) ! nat i) \<and> seq (m2 a1) ! (1 :: nat) = (1 :: int) \<longrightarrow> ((0 :: int) \<le> (1 :: int) \<and> (1 :: int) < int (length (seq (m2 b)))) \<and> (\<forall>(b1 :: int t2). seq (m2 b1) = (seq (m2 b))[nat (1 :: int) := 10 :: int] \<and> length (seq (m2 b1)) = length (seq (m2 b)) \<and> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < int (length (seq (m2 b)))) \<and> \<not>i = (1 :: int) \<longrightarrow> seq (m2 b1) ! nat i = seq (m2 b) ! nat i) \<and> seq (m2 b1) ! (1 :: nat) = (10 :: int) \<longrightarrow> ((0 :: int) \<le> (2 :: int) \<and> (2 :: int) < int (length (seq (m2 a1)))) \<and> (\<forall>(a2 :: int t2). seq (m2 a2) = (seq (m2 a1))[nat (2 :: int) := 2 :: int] \<and> length (seq (m2 a2)) = length (seq (m2 a1)) \<and> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < int (length (seq (m2 a1)))) \<and> \<not>i = (2 :: int) \<longrightarrow> seq (m2 a2) ! nat i = seq (m2 a1) ! nat i) \<and> seq (m2 a2) ! (2 :: nat) = (2 :: int) \<longrightarrow> ((0 :: int) \<le> (2 :: int) \<and> (2 :: int) < int (length (seq (m2 b1)))) \<and> (\<forall>(b2 :: int t2). seq (m2 b2) = (seq (m2 b1))[nat (2 :: int) := 20 :: int] \<and> length (seq (m2 b2)) = length (seq (m2 b1)) \<and> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < int (length (seq (m2 b1)))) \<and> \<not>i = (2 :: int) \<longrightarrow> seq (m2 b2) ! nat i = seq (m2 b1) ! nat i) \<and> seq (m2 b2) ! (2 :: nat) = (20 :: int) \<longrightarrow> (seq (m2 a2) ! (1 :: nat) = (1 :: int) \<and> seq (m2 a2) ! (42 :: nat) = (0 :: int)) \<and> (seq (m2 b2) ! (1 :: nat) = (10 :: int) \<and> seq (m2 b2) ! (42 :: nat) = (1 :: int)) \<and> ((0 :: int) \<le> (1 :: int) \<and> (1 :: int) < int (length (seq (m2 a2)))) \<and> (\<forall>(a3 :: int t2). seq (m2 a3) = take (1 :: nat) (seq (m2 a2)) @ drop (nat ((1 :: int) + (1 :: int))) (seq (m2 a2)) \<and> int (length (seq (m2 a3))) = int (length (seq (m2 a2))) - (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (1 :: int) \<longrightarrow> seq (m2 a3) ! nat i = seq (m2 a2) ! nat i) \<and> (\<forall>(i :: int). (1 :: int) \<le> i \<and> i < int (length (seq (m2 a3))) \<longrightarrow> seq (m2 a3) ! nat i = seq (m2 a2) ! nat (i + (1 :: int))) \<longrightarrow> ((0 :: int) \<le> (2 :: int) \<and> (2 :: int) < int (length (seq (m2 b2)))) \<and> (\<forall>(b3 :: int t2). seq (m2 b3) = take (2 :: nat) (seq (m2 b2)) @ drop (nat ((2 :: int) + (1 :: int))) (seq (m2 b2)) \<and> int (length (seq (m2 b3))) = int (length (seq (m2 b2))) - (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (2 :: int) \<longrightarrow> seq (m2 b3) ! nat i = seq (m2 b2) ! nat i) \<and> (\<forall>(i :: int). (2 :: int) \<le> i \<and> i < int (length (seq (m2 b3))) \<longrightarrow> seq (m2 b3) ! nat i = seq (m2 b2) ! nat (i + (1 :: int))) \<longrightarrow> (seq (m2 a3) ! (1 :: nat) = (2 :: int) \<and> seq (m2 a3) ! (42 :: nat) = (0 :: int)) \<and> seq (m2 b3) ! (2 :: nat) = (1 :: int) \<and> seq (m2 b3) ! (42 :: nat) = (1 :: int))))))"
  sorry
end
