theory blocking_semantics5_FreshVariables_cons_appendqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp"
begin
theorem cons_append'vc:
  fixes a :: "'a"
  fixes l1 :: "'a list"
  fixes l2 :: "'a list"
  shows "Cons a (l1 @ l2) = Cons a l1 @ l2"
  sorry
end
