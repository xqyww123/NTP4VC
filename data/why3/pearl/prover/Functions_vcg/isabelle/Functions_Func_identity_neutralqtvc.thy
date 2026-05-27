theory Functions_Func_identity_neutralqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Functions_Config"
begin
definition extensionalEqual :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> _"
  where "extensionalEqual f g \<longleftrightarrow> (\<forall>(x :: 'a). f x = g x)" for f g
axiomatization where functionExtensionality:   "f = g"
 if "extensionalEqual f g"
  for f :: "'a \<Rightarrow> 'b"
  and g :: "'a \<Rightarrow> 'b"
consts update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
axiomatization where update_def:   "update f x y z = (if x = z then y else f z)"
  for f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
  and y :: "'b"
  and z :: "'a"
consts identity :: "'a \<Rightarrow> 'a"
axiomatization where identity_def:   "identity x = x"
  for x :: "'a"
consts compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"
axiomatization where compose_def:   "compose g f x = g (f x)"
  for g :: "'b \<Rightarrow> 'c"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
theorem identity_neutral'vc:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "compose f identity = f"
  and "compose identity f = f"
  sorry
end
