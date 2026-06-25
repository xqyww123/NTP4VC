theory bitvector_examples_Test_from_bitvector_example_Test6
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded"
begin
theorem Test6:
  shows "(bit (((4294967295 :: 32 word) >> unat (1 :: 32 word)) >>> unat (16 :: 32 word)) (unat (16 :: 32 word))) = False"
  sorry
end
