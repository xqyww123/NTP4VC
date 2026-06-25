theory verifythis_2018_mind_the_gap_2_GapBuffer_deleteqtvc
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
definition contents_deleted :: "buffer \<Rightarrow> buffer \<Rightarrow> int \<Rightarrow> _"
  where "contents_deleted newb oldb pos \<longleftrightarrow> len_contents newb = len_contents oldb - (1 :: int) \<and> ((0 :: int) \<le> pos \<and> pos < len_contents oldb) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < pos \<longrightarrow> contents newb i = contents oldb i) \<and> (\<forall>(i :: int). pos \<le> i \<and> i < len_contents newb \<longrightarrow> contents newb i = contents oldb (i + (1 :: int)))" for newb oldb pos
theorem delete'vc:
  fixes b :: "buffer"
  shows "if \<not>l b = (0 :: int) then \<forall>(b1 :: buffer). ((0 :: int) \<le> l b - (1 :: int) \<and> l b - (1 :: int) \<le> r b \<and> r b \<le> int (length (data b))) \<and> (r b = r b1 \<and> l b - (1 :: int) = l b1 \<and> data b = data b1 \<longrightarrow> (if l b = (0 :: int) then b1 = b else l b1 = l b - (1 :: int) \<and> contents_deleted b1 b (l b - (1 :: int)))) else \<not>l b = (0 :: int) \<longrightarrow> l b = l b - (1 :: int) \<and> contents_deleted b b (l b - (1 :: int))"
  sorry
end
