theory udouble_UDouble
  imports "NTP4Verif.NTP4Verif" "Why3STD.ieee_float_RoundingMode"
begin
typedecl  udouble
consts to_real :: "udouble \<Rightarrow> real"
consts uround :: "mode \<Rightarrow> real \<Rightarrow> udouble"
axiomatization where uround_exact:   "uround m (to_real x) = x"
  for m :: "mode"
  and x :: "udouble"
consts uzero :: "udouble"
axiomatization where to_real_uzero:   "to_real uzero = (0 :: Real.real)"
consts utwo :: "udouble"
axiomatization where to_real_utwo:   "to_real utwo = (2 :: Real.real)"
definition uadd :: "udouble \<Rightarrow> udouble \<Rightarrow> udouble"
  where "uadd x y = uround RNE (to_real x + to_real y)" for x y
definition usub :: "udouble \<Rightarrow> udouble \<Rightarrow> udouble"
  where "usub x y = uround RNE (to_real x - to_real y)" for x y
definition umul :: "udouble \<Rightarrow> udouble \<Rightarrow> udouble"
  where "umul x y = uround RNE (to_real x * to_real y)" for x y
definition udiv :: "udouble \<Rightarrow> udouble \<Rightarrow> udouble"
  where "udiv x y = uround RNE (to_real x / to_real y)" for x y
definition uminus :: "udouble \<Rightarrow> udouble"
  where "uminus x = uround RNE (-to_real x)" for x
end
