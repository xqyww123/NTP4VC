theory tables_MapBase_selected_partqtvc
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
theorem selected_part'vc:
  fixes k :: "t1"
  fixes lseq :: "'a t list"
  fixes d :: "'a t"
  fixes rseq :: "'a t list"
  assumes fact0: "selection_possible k (lseq @ Cons d rseq)"
  shows "let kd :: t1 = key d; o1 :: 'a t list = Cons d rseq in int (length o1) = (1 :: int) + int (length rseq) \<and> o1 ! (0 :: nat) = d \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length rseq) \<longrightarrow> o1 ! nat i = rseq ! nat (i - (1 :: int))) \<longrightarrow> (let s :: 'a t list = lseq @ o1 in int (length s) = int (length lseq) + int (length o1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length lseq) \<longrightarrow> s ! nat i = lseq ! nat i) \<and> (\<forall>(i :: int). int (length lseq) \<le> i \<and> i < int (length s) \<longrightarrow> s ! nat i = o1 ! nat (i - int (length lseq))) \<longrightarrow> (\<forall>(cmp :: int). ((0 :: int) < cmp \<longleftrightarrow> lt kd k) \<and> (cmp < (0 :: int) \<longleftrightarrow> lt k kd) \<and> (cmp = (0 :: int) \<longleftrightarrow> eq k kd) \<longrightarrow> (\<forall>(result :: t1 part_base). (if cmp < (0 :: int) then result = Left k else if (0 :: int) < cmp then result = Right k else result = Here) \<longrightarrow> (case result of Here \<Rightarrow> selected k (split'mk lseq (Some d) rseq) | Left sl \<Rightarrow> selection_possible sl lseq \<and> (\<forall>(e :: 'a t split). selected sl e \<and> rebuild e = lseq \<longrightarrow> selected k (right_extend e d rseq)) | Right sr \<Rightarrow> selection_possible sr rseq \<and> (\<forall>(e :: 'a t split). selected sr e \<and> rebuild e = rseq \<longrightarrow> selected k (left_extend lseq d e))))))"
  sorry
end
