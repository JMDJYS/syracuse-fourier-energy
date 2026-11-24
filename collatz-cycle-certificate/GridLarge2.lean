import FastHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem r44982_1 : RangeCond 44982 45006 1 701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (1) (powMod (2^90065) 21 ((2^90065+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r44982_701 : RangeCond 44982 45006 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (701) (powMod (2^90065) 21 ((2^90065+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r44982_1401 : RangeCond 44982 45006 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (1401) (powMod (2^90065) 21 ((2^90065+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r44982_2101 : RangeCond 44982 45006 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (2101) (powMod (2^90065) 21 ((2^90065+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r44982_2801 : RangeCond 44982 45006 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (2801) (powMod (2^90065) 21 ((2^90065+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r44982_3501 : RangeCond 44982 45006 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (3501) (powMod (2^90065) 21 ((2^90065+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r44982_4201 : RangeCond 44982 45006 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (4201) (powMod (2^90065) 21 ((2^90065+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r44982_4901 : RangeCond 44982 45006 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (4901) (powMod (2^90065) 21 ((2^90065+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r44982_5601 : RangeCond 44982 45006 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (5601) (powMod (2^90065) 21 ((2^90065+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r44982_6301 : RangeCond 44982 45006 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (6301) (powMod (2^90065) 21 ((2^90065+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r44982_7001 : RangeCond 44982 45006 7001 7701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (7001) (powMod (2^90065) 21 ((2^90065+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r44982_7701 : RangeCond 44982 45006 7701 8401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (7701) (powMod (2^90065) 21 ((2^90065+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r44982_8401 : RangeCond 44982 45006 8401 9101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (8401) (powMod (2^90065) 21 ((2^90065+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r44982_9101 : RangeCond 44982 45006 9101 9801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (9101) (powMod (2^90065) 21 ((2^90065+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r44982_9801 : RangeCond 44982 45006 9801 10501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (9801) (powMod (2^90065) 21 ((2^90065+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r44982_10501 : RangeCond 44982 45006 10501 11201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (10501) (powMod (2^90065) 21 ((2^90065+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r44982_11201 : RangeCond 44982 45006 11201 11901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (11201) (powMod (2^90065) 21 ((2^90065+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r44982_11901 : RangeCond 44982 45006 11901 12601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (11901) (powMod (2^90065) 21 ((2^90065+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r44982_12601 : RangeCond 44982 45006 12601 13301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (12601) (powMod (2^90065) 21 ((2^90065+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r44982_13301 : RangeCond 44982 45006 13301 14001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (13301) (powMod (2^90065) 21 ((2^90065+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r44982_14001 : RangeCond 44982 45006 14001 14701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (14001) (powMod (2^90065) 21 ((2^90065+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r44982_14701 : RangeCond 44982 45006 14701 15401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (14701) (powMod (2^90065) 21 ((2^90065+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r44982_15401 : RangeCond 44982 45006 15401 16101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (15401) (powMod (2^90065) 21 ((2^90065+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r44982_16101 : RangeCond 44982 45006 16101 16801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (16101) (powMod (2^90065) 21 ((2^90065+1)/3) 16100 1) 700 = true by decide +kernel)

private theorem r44982_16801 : RangeCond 44982 45006 16801 17501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (16801) (powMod (2^90065) 21 ((2^90065+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r44982_17501 : RangeCond 44982 45006 17501 18201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (17501) (powMod (2^90065) 21 ((2^90065+1)/3) 17500 1) 700 = true by decide +kernel)

private theorem r44982_18201 : RangeCond 44982 45006 18201 18901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (18201) (powMod (2^90065) 21 ((2^90065+1)/3) 18200 1) 700 = true by decide +kernel)

private theorem r44982_18901 : RangeCond 44982 45006 18901 19601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (18901) (powMod (2^90065) 21 ((2^90065+1)/3) 18900 1) 700 = true by decide +kernel)

private theorem r44982_19601 : RangeCond 44982 45006 19601 20301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (19601) (powMod (2^90065) 21 ((2^90065+1)/3) 19600 1) 700 = true by decide +kernel)

private theorem r44982_20301 : RangeCond 44982 45006 20301 21001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (20301) (powMod (2^90065) 21 ((2^90065+1)/3) 20300 1) 700 = true by decide +kernel)

private theorem r44982_21001 : RangeCond 44982 45006 21001 21701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (21001) (powMod (2^90065) 21 ((2^90065+1)/3) 21000 1) 700 = true by decide +kernel)

private theorem r44982_21701 : RangeCond 44982 45006 21701 22401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (21701) (powMod (2^90065) 21 ((2^90065+1)/3) 21700 1) 700 = true by decide +kernel)

private theorem r44982_22401 : RangeCond 44982 45006 22401 23101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (22401) (powMod (2^90065) 21 ((2^90065+1)/3) 22400 1) 700 = true by decide +kernel)

private theorem r44982_23101 : RangeCond 44982 45006 23101 23801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (23101) (powMod (2^90065) 21 ((2^90065+1)/3) 23100 1) 700 = true by decide +kernel)

private theorem r44982_23801 : RangeCond 44982 45006 23801 24501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (23801) (powMod (2^90065) 21 ((2^90065+1)/3) 23800 1) 700 = true by decide +kernel)

private theorem r44982_24501 : RangeCond 44982 45006 24501 25201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (24501) (powMod (2^90065) 21 ((2^90065+1)/3) 24500 1) 700 = true by decide +kernel)

private theorem r44982_25201 : RangeCond 44982 45006 25201 25901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (25201) (powMod (2^90065) 21 ((2^90065+1)/3) 25200 1) 700 = true by decide +kernel)

private theorem r44982_25901 : RangeCond 44982 45006 25901 26601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (25901) (powMod (2^90065) 21 ((2^90065+1)/3) 25900 1) 700 = true by decide +kernel)

private theorem r44982_26601 : RangeCond 44982 45006 26601 27301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (26601) (powMod (2^90065) 21 ((2^90065+1)/3) 26600 1) 700 = true by decide +kernel)

private theorem r44982_27301 : RangeCond 44982 45006 27301 28001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (27301) (powMod (2^90065) 21 ((2^90065+1)/3) 27300 1) 700 = true by decide +kernel)

private theorem r44982_28001 : RangeCond 44982 45006 28001 28701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (28001) (powMod (2^90065) 21 ((2^90065+1)/3) 28000 1) 700 = true by decide +kernel)

private theorem r44982_28701 : RangeCond 44982 45006 28701 29401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (28701) (powMod (2^90065) 21 ((2^90065+1)/3) 28700 1) 700 = true by decide +kernel)

private theorem r44982_29401 : RangeCond 44982 45006 29401 30101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (29401) (powMod (2^90065) 21 ((2^90065+1)/3) 29400 1) 700 = true by decide +kernel)

private theorem r44982_30101 : RangeCond 44982 45006 30101 30801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (30101) (powMod (2^90065) 21 ((2^90065+1)/3) 30100 1) 700 = true by decide +kernel)

private theorem r44982_30801 : RangeCond 44982 45006 30801 31501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (30801) (powMod (2^90065) 21 ((2^90065+1)/3) 30800 1) 700 = true by decide +kernel)

private theorem r44982_31501 : RangeCond 44982 45006 31501 32201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (31501) (powMod (2^90065) 21 ((2^90065+1)/3) 31500 1) 700 = true by decide +kernel)

private theorem r44982_32201 : RangeCond 44982 45006 32201 32901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (32201) (powMod (2^90065) 21 ((2^90065+1)/3) 32200 1) 700 = true by decide +kernel)

private theorem r44982_32901 : RangeCond 44982 45006 32901 33601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (32901) (powMod (2^90065) 21 ((2^90065+1)/3) 32900 1) 700 = true by decide +kernel)

private theorem r44982_33601 : RangeCond 44982 45006 33601 34301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (33601) (powMod (2^90065) 21 ((2^90065+1)/3) 33600 1) 700 = true by decide +kernel)

private theorem r44982_34301 : RangeCond 44982 45006 34301 35001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (34301) (powMod (2^90065) 21 ((2^90065+1)/3) 34300 1) 700 = true by decide +kernel)

private theorem r44982_35001 : RangeCond 44982 45006 35001 35701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (35001) (powMod (2^90065) 21 ((2^90065+1)/3) 35000 1) 700 = true by decide +kernel)

private theorem r44982_35701 : RangeCond 44982 45006 35701 36401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (35701) (powMod (2^90065) 21 ((2^90065+1)/3) 35700 1) 700 = true by decide +kernel)

private theorem r44982_36401 : RangeCond 44982 45006 36401 37101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (36401) (powMod (2^90065) 21 ((2^90065+1)/3) 36400 1) 700 = true by decide +kernel)

private theorem r44982_37101 : RangeCond 44982 45006 37101 37801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (37101) (powMod (2^90065) 21 ((2^90065+1)/3) 37100 1) 700 = true by decide +kernel)

private theorem r44982_37801 : RangeCond 44982 45006 37801 38501 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (37801) (powMod (2^90065) 21 ((2^90065+1)/3) 37800 1) 700 = true by decide +kernel)

private theorem r44982_38501 : RangeCond 44982 45006 38501 39201 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (38501) (powMod (2^90065) 21 ((2^90065+1)/3) 38500 1) 700 = true by decide +kernel)

private theorem r44982_39201 : RangeCond 44982 45006 39201 39901 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (39201) (powMod (2^90065) 21 ((2^90065+1)/3) 39200 1) 700 = true by decide +kernel)

private theorem r44982_39901 : RangeCond 44982 45006 39901 40601 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (39901) (powMod (2^90065) 21 ((2^90065+1)/3) 39900 1) 700 = true by decide +kernel)

private theorem r44982_40601 : RangeCond 44982 45006 40601 41301 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (40601) (powMod (2^90065) 21 ((2^90065+1)/3) 40600 1) 700 = true by decide +kernel)

private theorem r44982_41301 : RangeCond 44982 45006 41301 42001 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (41301) (powMod (2^90065) 21 ((2^90065+1)/3) 41300 1) 700 = true by decide +kernel)

private theorem r44982_42001 : RangeCond 44982 45006 42001 42701 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (42001) (powMod (2^90065) 21 ((2^90065+1)/3) 42000 1) 700 = true by decide +kernel)

private theorem r44982_42701 : RangeCond 44982 45006 42701 43401 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (42701) (powMod (2^90065) 21 ((2^90065+1)/3) 42700 1) 700 = true by decide +kernel)

private theorem r44982_43401 : RangeCond 44982 45006 43401 44101 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (43401) (powMod (2^90065) 21 ((2^90065+1)/3) 43400 1) 700 = true by decide +kernel)

private theorem r44982_44101 : RangeCond 44982 45006 44101 44801 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (44101) (powMod (2^90065) 21 ((2^90065+1)/3) 44100 1) 700 = true by decide +kernel)

private theorem r44982_44801 : RangeCond 44982 45006 44801 44983 := by
  exact rangeCheck_sound (show rangeCheck 44982 45006 32 90065
    (44801) (powMod (2^90065) 21 ((2^90065+1)/3) 44800 1) 182 = true by decide +kernel)

theorem pairs44982 : AllPairs 44982 45006 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_1 r44982_701) (RangeCond.trans r44982_1401 r44982_2101)) (RangeCond.trans (RangeCond.trans r44982_2801 r44982_3501) (RangeCond.trans r44982_4201 r44982_4901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_5601 r44982_6301) (RangeCond.trans r44982_7001 r44982_7701)) (RangeCond.trans (RangeCond.trans r44982_8401 r44982_9101) (RangeCond.trans r44982_9801 r44982_10501)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_11201 r44982_11901) (RangeCond.trans r44982_12601 r44982_13301)) (RangeCond.trans (RangeCond.trans r44982_14001 r44982_14701) (RangeCond.trans r44982_15401 r44982_16101))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_16801 r44982_17501) (RangeCond.trans r44982_18201 r44982_18901)) (RangeCond.trans (RangeCond.trans r44982_19601 r44982_20301) (RangeCond.trans r44982_21001 r44982_21701))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_22401 r44982_23101) (RangeCond.trans r44982_23801 r44982_24501)) (RangeCond.trans (RangeCond.trans r44982_25201 r44982_25901) (RangeCond.trans r44982_26601 r44982_27301))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_28001 r44982_28701) (RangeCond.trans r44982_29401 r44982_30101)) (RangeCond.trans (RangeCond.trans r44982_30801 r44982_31501) (RangeCond.trans r44982_32201 r44982_32901)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_33601 r44982_34301) (RangeCond.trans r44982_35001 r44982_35701)) (RangeCond.trans (RangeCond.trans r44982_36401 r44982_37101) (RangeCond.trans r44982_37801 r44982_38501))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r44982_39201 r44982_39901) (RangeCond.trans r44982_40601 r44982_41301)) (RangeCond.trans (RangeCond.trans r44982_42001 r44982_42701) (RangeCond.trans r44982_43401 (RangeCond.trans r44982_44101 r44982_44801)))))))

#print axioms pairs44982

end Cycle108
