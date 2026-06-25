theory bitvector_examples_Test_from_bitvector_example_Test1
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded"
begin
theorem Test1:
  shows "(bit ((0 :: 32 word) AND (4294967295 :: 32 word)) (unat (1 :: 32 word))) = False"
  sorry
end
