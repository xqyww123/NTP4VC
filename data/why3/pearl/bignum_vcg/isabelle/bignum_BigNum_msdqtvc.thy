theory bignum_BigNum_msdqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts base :: "int"
axiomatization where base_def:   "(1 :: int) < base"
typedecl  digit
typedecl  num
fun "value" :: "int list \<Rightarrow> int"
  where "value (Nil :: int list) = (0 :: int)"
      | "value (Cons d r) = d + base * value r" for d r
fun valid :: "int list \<Rightarrow> _"
  where "valid (Nil :: int list) = True"
      | "valid (Cons d (Nil :: int list)) = ((0 :: int) < d \<and> d < base)" for d
      | "valid (Cons d r) = (((0 :: int) \<le> d \<and> d < base) \<and> valid r)" for d r
theorem msd'vc:
  fixes n :: "int list"
  assumes fact0: "valid n"
  shows "value n = (0 :: int) \<longleftrightarrow> n = (Nil :: int list)"
  sorry
end
