theory verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_mapaddleft_lengthqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  color = Red | Black
typedecl  coloring
definition tworedneighbors :: "color list \<Rightarrow> int \<Rightarrow> _"
  where "tworedneighbors c i \<longleftrightarrow> c ! nat (i - (2 :: int)) = Red \<and> c ! nat (i - (1 :: int)) = Red \<and> (2 :: int) \<le> i \<or> c ! nat (i - (1 :: int)) = Red \<and> c ! nat (i + (1 :: int)) = Red \<and> (1 :: int) \<le> i \<and> i \<le> int (length c) - (2 :: int) \<or> c ! nat (i + (1 :: int)) = Red \<and> c ! nat (i + (2 :: int)) = Red \<and> i \<le> int (length c) - (3 :: int)" for c i
definition valid :: "color list \<Rightarrow> _"
  where "valid c \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length c) \<longrightarrow> c ! nat i = Red \<longrightarrow> tworedneighbors c i)" for c
consts first_black_tile :: "color list \<Rightarrow> int"
axiomatization where first_black_tile_def:   "if int (length c) = (0 :: int) then first_black_tile c = (0 :: int) else (case c ! (0 :: nat) of Black \<Rightarrow> first_black_tile c = (0 :: int) | Red \<Rightarrow> first_black_tile c = (1 :: int) + first_black_tile (drop (1 :: nat) c))"
  for c :: "color list"
axiomatization where first_black_tile'spec'2'0:   "(0 :: int) \<le> first_black_tile c"
  for c :: "color list"
axiomatization where first_black_tile'spec'2'1:   "first_black_tile c \<le> int (length c)"
  for c :: "color list"
axiomatization where first_black_tile'spec'1:   "c ! nat j = Red"
 if "(0 :: int) \<le> j"
 and "j < first_black_tile c"
 and "first_black_tile c \<le> int (length c)"
  for j :: "int"
  and c :: "color list"
axiomatization where first_black_tile'spec'0:   "c ! nat (first_black_tile c) = Black"
 if "first_black_tile c < int (length c)"
  for c :: "color list"
axiomatization where first_black_tile'spec:   "first_black_tile c = (0 :: int) \<or> (3 :: int) \<le> first_black_tile c"
 if "valid c"
  for c :: "color list"
consts addleft :: "int \<Rightarrow> color list \<Rightarrow> color list"
axiomatization where addleft_def:   "if nr \<le> (0 :: int) then addleft nr c = Cons Black c else addleft nr c = Cons Red (addleft (nr - (1 :: int)) c)"
  for nr :: "int"
  and c :: "color list"
axiomatization where addleft'spec:   "int (length (addleft nr c)) = int (length c) + nr + (1 :: int)"
 if "(0 :: int) \<le> nr"
  for nr :: "int"
  and c :: "color list"
consts addleft_closure :: "int \<Rightarrow> color list \<Rightarrow> color list"
axiomatization where addleft_closure_def:   "addleft_closure y y1 = addleft y y1"
  for y :: "int"
  and y1 :: "color list"
definition mapaddleft :: "color list fset \<Rightarrow> int \<Rightarrow> color list fset"
  where "mapaddleft s nr = addleft_closure nr |`| s" for s nr
definition reciprocal :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> _"
  where "reciprocal f g \<longleftrightarrow> (\<forall>(y :: 'a). g (f y) = y)" for f g
definition rmleft :: "int \<Rightarrow> color list \<Rightarrow> color list"
  where "rmleft nr c = drop (nat (nr + (1 :: int))) c" for nr c
theorem mapaddleft_length'vc:
  fixes s :: "color list fset"
  fixes l1 :: "int"
  fixes nr :: "int"
  fixes c :: "color list"
  assumes fact0: "\<forall>(c :: color list). c |\<in>| s \<longrightarrow> int (length c) = l1"
  assumes fact1: "(0 :: int) \<le> nr"
  assumes fact2: "c |\<in>| mapaddleft s nr"
  shows "int (length c) = l1 + nr + (1 :: int)"
  sorry
end
