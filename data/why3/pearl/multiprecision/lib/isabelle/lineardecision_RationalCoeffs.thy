theory lineardecision_RationalCoeffs
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
typedecl  rvars
definition rinterp :: "int \<times> int \<Rightarrow> (int \<Rightarrow> real) \<Rightarrow> real"
  where "rinterp t1 x_v = (case t1 of (n, d) \<Rightarrow> real_of_int n / real_of_int d)" for t1 x_v
definition req :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> _"
  where "req a b \<longleftrightarrow> (case (a, b) of ((n1, d1), (n2, d2)) \<Rightarrow> n1 = n2 \<and> d1 = d2 \<or> \<not>d1 = (0 :: int) \<and> \<not>d2 = (0 :: int) \<and> n1 * d2 = n2 * d1)" for a b
axiomatization where req'spec:   "rinterp a y = rinterp b y"
 if "req a b"
  for a :: "int \<times> int"
  and b :: "int \<times> int"
  and y :: "int \<Rightarrow> real"
end
