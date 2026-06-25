theory verifythis_2018_mind_the_gap_2_GapBuffer_leftqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
consts dummy_char :: "char"
typedecl  buffer
consts data :: "buffer \<Rightarrow> char list"
consts l :: "buffer \<Rightarrow> int"
consts r :: "buffer \<Rightarrow> int"
axiomatization where buffer'invariant'0:   "(0 :: int) \<le> l self"
  for self :: "buffer"
axiomatization where buffer'invariant'1:   "l self \<le> r self"
  for self :: "buffer"
axiomatization where buffer'invariant'2:   "r self \<le> int (length (data self))"
  for self :: "buffer"
definition buffer'eq :: "buffer \<Rightarrow> buffer \<Rightarrow> _"
  where "buffer'eq a b \<longleftrightarrow> data a = data b \<and> l a = l b \<and> r a = r b" for a b
axiomatization where buffer'inj:   "a = b"
 if "buffer'eq a b"
  for a :: "buffer"
  and b :: "buffer"
definition len_contents :: "buffer \<Rightarrow> int"
  where "len_contents b = int (length (data b)) - r b + l b" for b
consts contents :: "buffer \<Rightarrow> int \<Rightarrow> char"
axiomatization where contents_def:   "contents b i = (if (0 :: int) \<le> i \<and> i < l b then (nth (data b) o nat) i else if l b \<le> i \<and> i \<le> len_contents b then (nth (data b) o nat) (i + r b - l b) else dummy_char)"
  for b :: "buffer"
  and i :: "int"
definition same_contents :: "buffer \<Rightarrow> buffer \<Rightarrow> _"
  where "same_contents b1 b2 \<longleftrightarrow> len_contents b1 = len_contents b2 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < len_contents b1 \<longrightarrow> contents b1 i = contents b2 i)" for b1 b2
theorem left'vc:
  fixes b :: "buffer"
  shows "if \<not>l b = (0 :: int) then ((0 :: int) \<le> l b - (1 :: int) \<and> l b - (1 :: int) < int (length (data b))) \<and> (let o1 :: char = data b ! nat (l b - (1 :: int)) in ((0 :: int) \<le> r b - (1 :: int) \<and> r b - (1 :: int) < int (length (data b))) \<and> (\<forall>(b1 :: buffer). length ((data b)[nat (r b - (1 :: int)) := o1]) = length (data b) \<longrightarrow> length ((data b)[nat (r b - (1 :: int)) := o1]) = length (data b) \<longrightarrow> nth ((data b)[nat (r b - (1 :: int)) := o1]) o nat = (nth (data b) o nat)(r b - (1 :: int) := o1) \<longrightarrow> ((0 :: int) \<le> l b - (1 :: int) \<and> l b - (1 :: int) \<le> r b - (1 :: int) \<and> r b - (1 :: int) \<le> int (length ((data b)[nat (r b - (1 :: int)) := o1]))) \<and> (r b - (1 :: int) = r b1 \<and> l b - (1 :: int) = l b1 \<and> (data b)[nat (r b - (1 :: int)) := o1] = data b1 \<longrightarrow> (if l b = (0 :: int) then b1 = b else l b1 = l b - (1 :: int)) \<and> same_contents b1 b))) else (\<not>l b = (0 :: int) \<longrightarrow> l b = l b - (1 :: int)) \<and> same_contents b b"
  sorry
end
