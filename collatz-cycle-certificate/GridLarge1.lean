import FastHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem r28371_1 : RangeCond 28371 28395 1 701 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (1) (powMod (2^56843) 21 ((2^56843+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r28371_701 : RangeCond 28371 28395 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (701) (powMod (2^56843) 21 ((2^56843+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r28371_1401 : RangeCond 28371 28395 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (1401) (powMod (2^56843) 21 ((2^56843+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r28371_2101 : RangeCond 28371 28395 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (2101) (powMod (2^56843) 21 ((2^56843+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r28371_2801 : RangeCond 28371 28395 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (2801) (powMod (2^56843) 21 ((2^56843+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r28371_3501 : RangeCond 28371 28395 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (3501) (powMod (2^56843) 21 ((2^56843+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r28371_4201 : RangeCond 28371 28395 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (4201) (powMod (2^56843) 21 ((2^56843+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r28371_4901 : RangeCond 28371 28395 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (4901) (powMod (2^56843) 21 ((2^56843+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r28371_5601 : RangeCond 28371 28395 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (5601) (powMod (2^56843) 21 ((2^56843+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r28371_6301 : RangeCond 28371 28395 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (6301) (powMod (2^56843) 21 ((2^56843+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r28371_7001 : RangeCond 28371 28395 7001 7701 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (7001) (powMod (2^56843) 21 ((2^56843+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r28371_7701 : RangeCond 28371 28395 7701 8401 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (7701) (powMod (2^56843) 21 ((2^56843+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r28371_8401 : RangeCond 28371 28395 8401 9101 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (8401) (powMod (2^56843) 21 ((2^56843+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r28371_9101 : RangeCond 28371 28395 9101 9801 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (9101) (powMod (2^56843) 21 ((2^56843+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r28371_9801 : RangeCond 28371 28395 9801 10501 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (9801) (powMod (2^56843) 21 ((2^56843+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r28371_10501 : RangeCond 28371 28395 10501 11201 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (10501) (powMod (2^56843) 21 ((2^56843+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r28371_11201 : RangeCond 28371 28395 11201 11901 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (11201) (powMod (2^56843) 21 ((2^56843+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r28371_11901 : RangeCond 28371 28395 11901 12601 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (11901) (powMod (2^56843) 21 ((2^56843+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r28371_12601 : RangeCond 28371 28395 12601 13301 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (12601) (powMod (2^56843) 21 ((2^56843+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r28371_13301 : RangeCond 28371 28395 13301 14001 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (13301) (powMod (2^56843) 21 ((2^56843+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r28371_14001 : RangeCond 28371 28395 14001 14701 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (14001) (powMod (2^56843) 21 ((2^56843+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r28371_14701 : RangeCond 28371 28395 14701 15401 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (14701) (powMod (2^56843) 21 ((2^56843+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r28371_15401 : RangeCond 28371 28395 15401 16101 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (15401) (powMod (2^56843) 21 ((2^56843+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r28371_16101 : RangeCond 28371 28395 16101 16801 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (16101) (powMod (2^56843) 21 ((2^56843+1)/3) 16100 1) 700 = true by decide +kernel)

private theorem r28371_16801 : RangeCond 28371 28395 16801 17501 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (16801) (powMod (2^56843) 21 ((2^56843+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r28371_17501 : RangeCond 28371 28395 17501 18201 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (17501) (powMod (2^56843) 21 ((2^56843+1)/3) 17500 1) 700 = true by decide +kernel)

private theorem r28371_18201 : RangeCond 28371 28395 18201 18901 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (18201) (powMod (2^56843) 21 ((2^56843+1)/3) 18200 1) 700 = true by decide +kernel)

private theorem r28371_18901 : RangeCond 28371 28395 18901 19601 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (18901) (powMod (2^56843) 21 ((2^56843+1)/3) 18900 1) 700 = true by decide +kernel)

private theorem r28371_19601 : RangeCond 28371 28395 19601 20301 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (19601) (powMod (2^56843) 21 ((2^56843+1)/3) 19600 1) 700 = true by decide +kernel)

private theorem r28371_20301 : RangeCond 28371 28395 20301 21001 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (20301) (powMod (2^56843) 21 ((2^56843+1)/3) 20300 1) 700 = true by decide +kernel)

private theorem r28371_21001 : RangeCond 28371 28395 21001 21701 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (21001) (powMod (2^56843) 21 ((2^56843+1)/3) 21000 1) 700 = true by decide +kernel)

private theorem r28371_21701 : RangeCond 28371 28395 21701 22401 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (21701) (powMod (2^56843) 21 ((2^56843+1)/3) 21700 1) 700 = true by decide +kernel)

private theorem r28371_22401 : RangeCond 28371 28395 22401 23101 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (22401) (powMod (2^56843) 21 ((2^56843+1)/3) 22400 1) 700 = true by decide +kernel)

private theorem r28371_23101 : RangeCond 28371 28395 23101 23801 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (23101) (powMod (2^56843) 21 ((2^56843+1)/3) 23100 1) 700 = true by decide +kernel)

private theorem r28371_23801 : RangeCond 28371 28395 23801 24501 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (23801) (powMod (2^56843) 21 ((2^56843+1)/3) 23800 1) 700 = true by decide +kernel)

private theorem r28371_24501 : RangeCond 28371 28395 24501 25201 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (24501) (powMod (2^56843) 21 ((2^56843+1)/3) 24500 1) 700 = true by decide +kernel)

private theorem r28371_25201 : RangeCond 28371 28395 25201 25901 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (25201) (powMod (2^56843) 21 ((2^56843+1)/3) 25200 1) 700 = true by decide +kernel)

private theorem r28371_25901 : RangeCond 28371 28395 25901 26601 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (25901) (powMod (2^56843) 21 ((2^56843+1)/3) 25900 1) 700 = true by decide +kernel)

private theorem r28371_26601 : RangeCond 28371 28395 26601 27301 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (26601) (powMod (2^56843) 21 ((2^56843+1)/3) 26600 1) 700 = true by decide +kernel)

private theorem r28371_27301 : RangeCond 28371 28395 27301 28001 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (27301) (powMod (2^56843) 21 ((2^56843+1)/3) 27300 1) 700 = true by decide +kernel)

private theorem r28371_28001 : RangeCond 28371 28395 28001 28372 := by
  exact rangeCheck_sound (show rangeCheck 28371 28395 32 56843
    (28001) (powMod (2^56843) 21 ((2^56843+1)/3) 28000 1) 371 = true by decide +kernel)

theorem pairs28371 : AllPairs 28371 28395 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r28371_1 r28371_701) (RangeCond.trans r28371_1401 (RangeCond.trans r28371_2101 r28371_2801))) (RangeCond.trans (RangeCond.trans r28371_3501 r28371_4201) (RangeCond.trans r28371_4901 (RangeCond.trans r28371_5601 r28371_6301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r28371_7001 r28371_7701) (RangeCond.trans r28371_8401 (RangeCond.trans r28371_9101 r28371_9801))) (RangeCond.trans (RangeCond.trans r28371_10501 r28371_11201) (RangeCond.trans r28371_11901 (RangeCond.trans r28371_12601 r28371_13301))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r28371_14001 r28371_14701) (RangeCond.trans r28371_15401 (RangeCond.trans r28371_16101 r28371_16801))) (RangeCond.trans (RangeCond.trans r28371_17501 r28371_18201) (RangeCond.trans r28371_18901 (RangeCond.trans r28371_19601 r28371_20301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r28371_21001 r28371_21701) (RangeCond.trans r28371_22401 (RangeCond.trans r28371_23101 r28371_23801))) (RangeCond.trans (RangeCond.trans r28371_24501 (RangeCond.trans r28371_25201 r28371_25901)) (RangeCond.trans r28371_26601 (RangeCond.trans r28371_27301 r28371_28001))))))

#print axioms pairs28371

end Cycle108
