theory linked_list_rev_Termination_set_idxqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf"
begin
typedecl  loc
consts null :: "loc"
datatype  mem = mem'mk ("next": "loc \<Rightarrow> loc")
definition valid_cells :: "(int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> _"
  where "valid_cells s n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> \<not>s i = null) \<and> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: int) \<le> j \<and> j < n \<longrightarrow> \<not>i = j \<longrightarrow> \<not>s i = s j)" for s n
definition inside_memory :: "(int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> loc \<Rightarrow> _"
  where "inside_memory s n l \<longleftrightarrow> l = null \<or> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < n) \<and> l = s i)" for s n l
definition finite_memory :: "mem \<Rightarrow> (int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> _"
  where "finite_memory m s n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> inside_memory s n (next m (s i)))" for m s n
consts fc :: "(int \<Rightarrow> loc) \<Rightarrow> (loc \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc s idx i = True \<longleftrightarrow> (0 :: int) < idx (s i)"
  for s :: "int \<Rightarrow> loc"
  and idx :: "loc \<Rightarrow> int"
  and i :: "int"
definition seen :: "(int \<Rightarrow> loc) \<Rightarrow> (loc \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "seen s idx lo hi = numof (fc s idx) lo hi" for s idx lo hi
theorem set_idx'vc:
  fixes s :: "int \<Rightarrow> loc"
  fixes n :: "int"
  fixes l :: "loc"
  fixes idx :: "loc \<Rightarrow> int"
  assumes fact0: "valid_cells s n"
  assumes fact1: "inside_memory s n l"
  assumes fact2: "\<not>l = null"
  assumes fact3: "idx l = -(1 :: int)"
  assumes fact4: "(0 :: int) \<le> seen s idx (0 :: int) n"
  shows "seen s (idx(l := seen s idx (0 :: int) n + (1 :: int))) (0 :: int) n = (1 :: int) + seen s idx (0 :: int) n"
  sorry
end
