theory verifythis_2018_mind_the_gap_2_GapBuffer_growqtvc
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
theorem grow'vc:
  fixes b :: "buffer"
  shows "let o1 :: int = int (length (data b)) + (42 :: int) in (0 :: int) \<le> o1 \<and> (\<forall>(ndata :: char list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o1 \<longrightarrow> ndata ! nat i = dummy_char) \<and> int (length ndata) = o1 \<longrightarrow> (let o2 :: int = l b; o3 :: char list = data b in (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> o2 \<and> (0 :: int) + o2 \<le> int (length o3)) \<and> (0 :: int) \<le> (0 :: int) \<and> (0 :: int) + o2 \<le> int (length ndata)) \<and> (\<forall>(ndata1 :: char list). length ndata1 = length ndata \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (0 :: int) \<or> (0 :: int) + o2 \<le> i \<and> i < int (length ndata1) \<longrightarrow> ndata1 ! nat i = ndata ! nat i) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (0 :: int) + o2 \<longrightarrow> ndata1 ! nat i = o3 ! nat ((0 :: int) + i - (0 :: int))) \<longrightarrow> (let o4 :: int = int (length (data b)) - r b; o5 :: int = r b + (42 :: int); o6 :: int = r b; o7 :: char list = data b in (((0 :: int) \<le> o6 \<and> (0 :: int) \<le> o4 \<and> o6 + o4 \<le> int (length o7)) \<and> (0 :: int) \<le> o5 \<and> o5 + o4 \<le> int (length ndata1)) \<and> (\<forall>(ndata2 :: char list). length ndata2 = length ndata1 \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < o5 \<or> o5 + o4 \<le> i \<and> i < int (length ndata2) \<longrightarrow> ndata2 ! nat i = ndata1 ! nat i) \<and> (\<forall>(i :: int). o5 \<le> i \<and> i < o5 + o4 \<longrightarrow> ndata2 ! nat i = o7 ! nat (o6 + i - o5)) \<longrightarrow> (\<forall>(b1 :: buffer). ((0 :: int) \<le> l b \<and> l b \<le> r b + (42 :: int) \<and> r b + (42 :: int) \<le> int (length ndata2)) \<and> (r b + (42 :: int) = r b1 \<and> l b = l b1 \<and> ndata2 = data b1 \<longrightarrow> l b1 = l b \<and> r b1 = r b + (42 :: int) \<and> same_contents b1 b)))))))"
  sorry
end
