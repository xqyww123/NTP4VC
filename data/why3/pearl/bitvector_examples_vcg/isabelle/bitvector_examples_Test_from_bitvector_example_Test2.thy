theory bitvector_examples_Test_from_bitvector_example_Test2
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded"
begin
theorem Test2:
  shows "(bit ((4294967295 :: 32 word) >> unat (16 :: 32 word)) (unat (15 :: 32 word))) = True"
  sorry
end
