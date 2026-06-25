theory verifythis_2018_mind_the_gap_2_GapBuffer_insertqtvc
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
definition contents_inserted :: "buffer \<Rightarrow> buffer \<Rightarrow> char \<Rightarrow> int \<Rightarrow> _"
  where "contents_inserted newb oldb x pos \<longleftrightarrow> len_contents newb = len_contents oldb + (1 :: int) \<and> ((0 :: int) \<le> pos \<and> pos \<le> len_contents oldb) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < pos \<longrightarrow> contents newb i = contents oldb i) \<and> contents newb pos = x \<and> (\<forall>(i :: int). pos < i \<and> i < len_contents newb \<longrightarrow> contents newb i = contents oldb (i - (1 :: int)))" for newb oldb x pos
theorem insert'vc:
  fixes b :: "buffer"
  fixes x :: "char"
  shows "if l b = r b then \<forall>(b1 :: buffer). l b = l b1 \<longrightarrow> l b1 = l b \<and> r b1 = r b + (42 :: int) \<and> same_contents b1 b \<longrightarrow> (let o1 :: int = l b1; o2 :: char list = data b1 in ((0 :: int) \<le> o1 \<and> o1 < int (length o2)) \<and> (length (o2[nat o1 := x]) = length o2 \<longrightarrow> length (o2[nat o1 := x]) = length (data b1) \<longrightarrow> nth (o2[nat o1 := x]) o nat = (nth o2 o nat)(o1 := x) \<longrightarrow> (\<forall>(b2 :: buffer). ((0 :: int) \<le> l b1 + (1 :: int) \<and> l b1 + (1 :: int) \<le> r b1 \<and> r b1 \<le> int (length (o2[nat o1 := x]))) \<and> (r b1 = r b2 \<and> l b1 + (1 :: int) = l b2 \<and> o2[nat o1 := x] = data b2 \<longrightarrow> l b2 = l b + (1 :: int) \<and> contents_inserted b2 b x (l b))))) else let o1 :: int = l b; o2 :: char list = data b in ((0 :: int) \<le> o1 \<and> o1 < int (length o2)) \<and> (length (o2[nat o1 := x]) = length o2 \<longrightarrow> length (o2[nat o1 := x]) = length (data b) \<longrightarrow> nth (o2[nat o1 := x]) o nat = (nth o2 o nat)(o1 := x) \<longrightarrow> (\<forall>(b1 :: buffer). ((0 :: int) \<le> l b + (1 :: int) \<and> l b + (1 :: int) \<le> r b \<and> r b \<le> int (length (o2[nat o1 := x]))) \<and> (r b = r b1 \<and> l b + (1 :: int) = l b1 \<and> o2[nat o1 := x] = data b1 \<longrightarrow> l b1 = l b + (1 :: int) \<and> contents_inserted b1 b x (l b))))"
  sorry
end
