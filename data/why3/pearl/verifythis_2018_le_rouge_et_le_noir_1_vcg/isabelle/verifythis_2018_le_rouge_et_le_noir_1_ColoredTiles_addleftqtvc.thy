theory verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_addleftqtvc
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
theorem addleft'vc:
  fixes nr :: "int"
  fixes c :: "color list"
  shows "\<not>nr \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> nr \<and> nr - (1 :: int) < nr"
  and "\<forall>(result :: color list). (if nr \<le> (0 :: int) then let o1 :: color = Black in result = Cons o1 c \<and> int (length result) = (1 :: int) + int (length c) \<and> result ! (0 :: nat) = o1 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length c) \<longrightarrow> result ! nat i = c ! nat (i - (1 :: int))) else let o1 :: int = nr - (1 :: int) in \<exists>(o2 :: color list). ((0 :: int) \<le> o1 \<longrightarrow> int (length o2) = int (length c) + o1 + (1 :: int)) \<and> (let o3 :: color = Red in result = Cons o3 o2 \<and> int (length result) = (1 :: int) + int (length o2) \<and> result ! (0 :: nat) = o3 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length o2) \<longrightarrow> result ! nat i = o2 ! nat (i - (1 :: int))))) \<longrightarrow> (0 :: int) \<le> nr \<longrightarrow> int (length result) = int (length c) + nr + (1 :: int)"
  sorry
end
