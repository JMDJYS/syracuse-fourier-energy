import FastHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem r71309_1 : RangeCond 71309 71333 1 701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (1) (powMod (2^142719) 21 ((2^142719+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r71309_701 : RangeCond 71309 71333 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (701) (powMod (2^142719) 21 ((2^142719+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r71309_1401 : RangeCond 71309 71333 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (1401) (powMod (2^142719) 21 ((2^142719+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r71309_2101 : RangeCond 71309 71333 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (2101) (powMod (2^142719) 21 ((2^142719+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r71309_2801 : RangeCond 71309 71333 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (2801) (powMod (2^142719) 21 ((2^142719+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r71309_3501 : RangeCond 71309 71333 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (3501) (powMod (2^142719) 21 ((2^142719+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r71309_4201 : RangeCond 71309 71333 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (4201) (powMod (2^142719) 21 ((2^142719+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r71309_4901 : RangeCond 71309 71333 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (4901) (powMod (2^142719) 21 ((2^142719+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r71309_5601 : RangeCond 71309 71333 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (5601) (powMod (2^142719) 21 ((2^142719+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r71309_6301 : RangeCond 71309 71333 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (6301) (powMod (2^142719) 21 ((2^142719+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r71309_7001 : RangeCond 71309 71333 7001 7701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (7001) (powMod (2^142719) 21 ((2^142719+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r71309_7701 : RangeCond 71309 71333 7701 8401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (7701) (powMod (2^142719) 21 ((2^142719+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r71309_8401 : RangeCond 71309 71333 8401 9101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (8401) (powMod (2^142719) 21 ((2^142719+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r71309_9101 : RangeCond 71309 71333 9101 9801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (9101) (powMod (2^142719) 21 ((2^142719+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r71309_9801 : RangeCond 71309 71333 9801 10501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (9801) (powMod (2^142719) 21 ((2^142719+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r71309_10501 : RangeCond 71309 71333 10501 11201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (10501) (powMod (2^142719) 21 ((2^142719+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r71309_11201 : RangeCond 71309 71333 11201 11901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (11201) (powMod (2^142719) 21 ((2^142719+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r71309_11901 : RangeCond 71309 71333 11901 12601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (11901) (powMod (2^142719) 21 ((2^142719+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r71309_12601 : RangeCond 71309 71333 12601 13301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (12601) (powMod (2^142719) 21 ((2^142719+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r71309_13301 : RangeCond 71309 71333 13301 14001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (13301) (powMod (2^142719) 21 ((2^142719+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r71309_14001 : RangeCond 71309 71333 14001 14701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (14001) (powMod (2^142719) 21 ((2^142719+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r71309_14701 : RangeCond 71309 71333 14701 15401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (14701) (powMod (2^142719) 21 ((2^142719+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r71309_15401 : RangeCond 71309 71333 15401 16101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (15401) (powMod (2^142719) 21 ((2^142719+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r71309_16101 : RangeCond 71309 71333 16101 16801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (16101) (powMod (2^142719) 21 ((2^142719+1)/3) 16100 1) 700 = true by decide +kernel)

private theorem r71309_16801 : RangeCond 71309 71333 16801 17501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (16801) (powMod (2^142719) 21 ((2^142719+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r71309_17501 : RangeCond 71309 71333 17501 18201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (17501) (powMod (2^142719) 21 ((2^142719+1)/3) 17500 1) 700 = true by decide +kernel)

private theorem r71309_18201 : RangeCond 71309 71333 18201 18901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (18201) (powMod (2^142719) 21 ((2^142719+1)/3) 18200 1) 700 = true by decide +kernel)

private theorem r71309_18901 : RangeCond 71309 71333 18901 19601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (18901) (powMod (2^142719) 21 ((2^142719+1)/3) 18900 1) 700 = true by decide +kernel)

private theorem r71309_19601 : RangeCond 71309 71333 19601 20301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (19601) (powMod (2^142719) 21 ((2^142719+1)/3) 19600 1) 700 = true by decide +kernel)

private theorem r71309_20301 : RangeCond 71309 71333 20301 21001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (20301) (powMod (2^142719) 21 ((2^142719+1)/3) 20300 1) 700 = true by decide +kernel)

private theorem r71309_21001 : RangeCond 71309 71333 21001 21701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (21001) (powMod (2^142719) 21 ((2^142719+1)/3) 21000 1) 700 = true by decide +kernel)

private theorem r71309_21701 : RangeCond 71309 71333 21701 22401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (21701) (powMod (2^142719) 21 ((2^142719+1)/3) 21700 1) 700 = true by decide +kernel)

private theorem r71309_22401 : RangeCond 71309 71333 22401 23101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (22401) (powMod (2^142719) 21 ((2^142719+1)/3) 22400 1) 700 = true by decide +kernel)

private theorem r71309_23101 : RangeCond 71309 71333 23101 23801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (23101) (powMod (2^142719) 21 ((2^142719+1)/3) 23100 1) 700 = true by decide +kernel)

private theorem r71309_23801 : RangeCond 71309 71333 23801 24501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (23801) (powMod (2^142719) 21 ((2^142719+1)/3) 23800 1) 700 = true by decide +kernel)

private theorem r71309_24501 : RangeCond 71309 71333 24501 25201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (24501) (powMod (2^142719) 21 ((2^142719+1)/3) 24500 1) 700 = true by decide +kernel)

private theorem r71309_25201 : RangeCond 71309 71333 25201 25901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (25201) (powMod (2^142719) 21 ((2^142719+1)/3) 25200 1) 700 = true by decide +kernel)

private theorem r71309_25901 : RangeCond 71309 71333 25901 26601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (25901) (powMod (2^142719) 21 ((2^142719+1)/3) 25900 1) 700 = true by decide +kernel)

private theorem r71309_26601 : RangeCond 71309 71333 26601 27301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (26601) (powMod (2^142719) 21 ((2^142719+1)/3) 26600 1) 700 = true by decide +kernel)

private theorem r71309_27301 : RangeCond 71309 71333 27301 28001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (27301) (powMod (2^142719) 21 ((2^142719+1)/3) 27300 1) 700 = true by decide +kernel)

private theorem r71309_28001 : RangeCond 71309 71333 28001 28701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (28001) (powMod (2^142719) 21 ((2^142719+1)/3) 28000 1) 700 = true by decide +kernel)

private theorem r71309_28701 : RangeCond 71309 71333 28701 29401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (28701) (powMod (2^142719) 21 ((2^142719+1)/3) 28700 1) 700 = true by decide +kernel)

private theorem r71309_29401 : RangeCond 71309 71333 29401 30101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (29401) (powMod (2^142719) 21 ((2^142719+1)/3) 29400 1) 700 = true by decide +kernel)

private theorem r71309_30101 : RangeCond 71309 71333 30101 30801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (30101) (powMod (2^142719) 21 ((2^142719+1)/3) 30100 1) 700 = true by decide +kernel)

private theorem r71309_30801 : RangeCond 71309 71333 30801 31501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (30801) (powMod (2^142719) 21 ((2^142719+1)/3) 30800 1) 700 = true by decide +kernel)

private theorem r71309_31501 : RangeCond 71309 71333 31501 32201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (31501) (powMod (2^142719) 21 ((2^142719+1)/3) 31500 1) 700 = true by decide +kernel)

private theorem r71309_32201 : RangeCond 71309 71333 32201 32901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (32201) (powMod (2^142719) 21 ((2^142719+1)/3) 32200 1) 700 = true by decide +kernel)

private theorem r71309_32901 : RangeCond 71309 71333 32901 33601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (32901) (powMod (2^142719) 21 ((2^142719+1)/3) 32900 1) 700 = true by decide +kernel)

private theorem r71309_33601 : RangeCond 71309 71333 33601 34301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (33601) (powMod (2^142719) 21 ((2^142719+1)/3) 33600 1) 700 = true by decide +kernel)

private theorem r71309_34301 : RangeCond 71309 71333 34301 35001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (34301) (powMod (2^142719) 21 ((2^142719+1)/3) 34300 1) 700 = true by decide +kernel)

private theorem r71309_35001 : RangeCond 71309 71333 35001 35701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (35001) (powMod (2^142719) 21 ((2^142719+1)/3) 35000 1) 700 = true by decide +kernel)

private theorem r71309_35701 : RangeCond 71309 71333 35701 36401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (35701) (powMod (2^142719) 21 ((2^142719+1)/3) 35700 1) 700 = true by decide +kernel)

private theorem r71309_36401 : RangeCond 71309 71333 36401 37101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (36401) (powMod (2^142719) 21 ((2^142719+1)/3) 36400 1) 700 = true by decide +kernel)

private theorem r71309_37101 : RangeCond 71309 71333 37101 37801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (37101) (powMod (2^142719) 21 ((2^142719+1)/3) 37100 1) 700 = true by decide +kernel)

private theorem r71309_37801 : RangeCond 71309 71333 37801 38501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (37801) (powMod (2^142719) 21 ((2^142719+1)/3) 37800 1) 700 = true by decide +kernel)

private theorem r71309_38501 : RangeCond 71309 71333 38501 39201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (38501) (powMod (2^142719) 21 ((2^142719+1)/3) 38500 1) 700 = true by decide +kernel)

private theorem r71309_39201 : RangeCond 71309 71333 39201 39901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (39201) (powMod (2^142719) 21 ((2^142719+1)/3) 39200 1) 700 = true by decide +kernel)

private theorem r71309_39901 : RangeCond 71309 71333 39901 40601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (39901) (powMod (2^142719) 21 ((2^142719+1)/3) 39900 1) 700 = true by decide +kernel)

private theorem r71309_40601 : RangeCond 71309 71333 40601 41301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (40601) (powMod (2^142719) 21 ((2^142719+1)/3) 40600 1) 700 = true by decide +kernel)

private theorem r71309_41301 : RangeCond 71309 71333 41301 42001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (41301) (powMod (2^142719) 21 ((2^142719+1)/3) 41300 1) 700 = true by decide +kernel)

private theorem r71309_42001 : RangeCond 71309 71333 42001 42701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (42001) (powMod (2^142719) 21 ((2^142719+1)/3) 42000 1) 700 = true by decide +kernel)

private theorem r71309_42701 : RangeCond 71309 71333 42701 43401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (42701) (powMod (2^142719) 21 ((2^142719+1)/3) 42700 1) 700 = true by decide +kernel)

private theorem r71309_43401 : RangeCond 71309 71333 43401 44101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (43401) (powMod (2^142719) 21 ((2^142719+1)/3) 43400 1) 700 = true by decide +kernel)

private theorem r71309_44101 : RangeCond 71309 71333 44101 44801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (44101) (powMod (2^142719) 21 ((2^142719+1)/3) 44100 1) 700 = true by decide +kernel)

private theorem r71309_44801 : RangeCond 71309 71333 44801 45501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (44801) (powMod (2^142719) 21 ((2^142719+1)/3) 44800 1) 700 = true by decide +kernel)

private theorem r71309_45501 : RangeCond 71309 71333 45501 46201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (45501) (powMod (2^142719) 21 ((2^142719+1)/3) 45500 1) 700 = true by decide +kernel)

private theorem r71309_46201 : RangeCond 71309 71333 46201 46901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (46201) (powMod (2^142719) 21 ((2^142719+1)/3) 46200 1) 700 = true by decide +kernel)

private theorem r71309_46901 : RangeCond 71309 71333 46901 47601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (46901) (powMod (2^142719) 21 ((2^142719+1)/3) 46900 1) 700 = true by decide +kernel)

private theorem r71309_47601 : RangeCond 71309 71333 47601 48301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (47601) (powMod (2^142719) 21 ((2^142719+1)/3) 47600 1) 700 = true by decide +kernel)

private theorem r71309_48301 : RangeCond 71309 71333 48301 49001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (48301) (powMod (2^142719) 21 ((2^142719+1)/3) 48300 1) 700 = true by decide +kernel)

private theorem r71309_49001 : RangeCond 71309 71333 49001 49701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (49001) (powMod (2^142719) 21 ((2^142719+1)/3) 49000 1) 700 = true by decide +kernel)

private theorem r71309_49701 : RangeCond 71309 71333 49701 50401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (49701) (powMod (2^142719) 21 ((2^142719+1)/3) 49700 1) 700 = true by decide +kernel)

private theorem r71309_50401 : RangeCond 71309 71333 50401 51101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (50401) (powMod (2^142719) 21 ((2^142719+1)/3) 50400 1) 700 = true by decide +kernel)

private theorem r71309_51101 : RangeCond 71309 71333 51101 51801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (51101) (powMod (2^142719) 21 ((2^142719+1)/3) 51100 1) 700 = true by decide +kernel)

private theorem r71309_51801 : RangeCond 71309 71333 51801 52501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (51801) (powMod (2^142719) 21 ((2^142719+1)/3) 51800 1) 700 = true by decide +kernel)

private theorem r71309_52501 : RangeCond 71309 71333 52501 53201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (52501) (powMod (2^142719) 21 ((2^142719+1)/3) 52500 1) 700 = true by decide +kernel)

private theorem r71309_53201 : RangeCond 71309 71333 53201 53901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (53201) (powMod (2^142719) 21 ((2^142719+1)/3) 53200 1) 700 = true by decide +kernel)

private theorem r71309_53901 : RangeCond 71309 71333 53901 54601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (53901) (powMod (2^142719) 21 ((2^142719+1)/3) 53900 1) 700 = true by decide +kernel)

private theorem r71309_54601 : RangeCond 71309 71333 54601 55301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (54601) (powMod (2^142719) 21 ((2^142719+1)/3) 54600 1) 700 = true by decide +kernel)

private theorem r71309_55301 : RangeCond 71309 71333 55301 56001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (55301) (powMod (2^142719) 21 ((2^142719+1)/3) 55300 1) 700 = true by decide +kernel)

private theorem r71309_56001 : RangeCond 71309 71333 56001 56701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (56001) (powMod (2^142719) 21 ((2^142719+1)/3) 56000 1) 700 = true by decide +kernel)

private theorem r71309_56701 : RangeCond 71309 71333 56701 57401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (56701) (powMod (2^142719) 21 ((2^142719+1)/3) 56700 1) 700 = true by decide +kernel)

private theorem r71309_57401 : RangeCond 71309 71333 57401 58101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (57401) (powMod (2^142719) 21 ((2^142719+1)/3) 57400 1) 700 = true by decide +kernel)

private theorem r71309_58101 : RangeCond 71309 71333 58101 58801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (58101) (powMod (2^142719) 21 ((2^142719+1)/3) 58100 1) 700 = true by decide +kernel)

private theorem r71309_58801 : RangeCond 71309 71333 58801 59501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (58801) (powMod (2^142719) 21 ((2^142719+1)/3) 58800 1) 700 = true by decide +kernel)

private theorem r71309_59501 : RangeCond 71309 71333 59501 60201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (59501) (powMod (2^142719) 21 ((2^142719+1)/3) 59500 1) 700 = true by decide +kernel)

private theorem r71309_60201 : RangeCond 71309 71333 60201 60901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (60201) (powMod (2^142719) 21 ((2^142719+1)/3) 60200 1) 700 = true by decide +kernel)

private theorem r71309_60901 : RangeCond 71309 71333 60901 61601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (60901) (powMod (2^142719) 21 ((2^142719+1)/3) 60900 1) 700 = true by decide +kernel)

private theorem r71309_61601 : RangeCond 71309 71333 61601 62301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (61601) (powMod (2^142719) 21 ((2^142719+1)/3) 61600 1) 700 = true by decide +kernel)

private theorem r71309_62301 : RangeCond 71309 71333 62301 63001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (62301) (powMod (2^142719) 21 ((2^142719+1)/3) 62300 1) 700 = true by decide +kernel)

private theorem r71309_63001 : RangeCond 71309 71333 63001 63701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (63001) (powMod (2^142719) 21 ((2^142719+1)/3) 63000 1) 700 = true by decide +kernel)

private theorem r71309_63701 : RangeCond 71309 71333 63701 64401 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (63701) (powMod (2^142719) 21 ((2^142719+1)/3) 63700 1) 700 = true by decide +kernel)

private theorem r71309_64401 : RangeCond 71309 71333 64401 65101 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (64401) (powMod (2^142719) 21 ((2^142719+1)/3) 64400 1) 700 = true by decide +kernel)

private theorem r71309_65101 : RangeCond 71309 71333 65101 65801 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (65101) (powMod (2^142719) 21 ((2^142719+1)/3) 65100 1) 700 = true by decide +kernel)

private theorem r71309_65801 : RangeCond 71309 71333 65801 66501 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (65801) (powMod (2^142719) 21 ((2^142719+1)/3) 65800 1) 700 = true by decide +kernel)

private theorem r71309_66501 : RangeCond 71309 71333 66501 67201 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (66501) (powMod (2^142719) 21 ((2^142719+1)/3) 66500 1) 700 = true by decide +kernel)

private theorem r71309_67201 : RangeCond 71309 71333 67201 67901 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (67201) (powMod (2^142719) 21 ((2^142719+1)/3) 67200 1) 700 = true by decide +kernel)

private theorem r71309_67901 : RangeCond 71309 71333 67901 68601 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (67901) (powMod (2^142719) 21 ((2^142719+1)/3) 67900 1) 700 = true by decide +kernel)

private theorem r71309_68601 : RangeCond 71309 71333 68601 69301 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (68601) (powMod (2^142719) 21 ((2^142719+1)/3) 68600 1) 700 = true by decide +kernel)

private theorem r71309_69301 : RangeCond 71309 71333 69301 70001 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (69301) (powMod (2^142719) 21 ((2^142719+1)/3) 69300 1) 700 = true by decide +kernel)

private theorem r71309_70001 : RangeCond 71309 71333 70001 70701 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (70001) (powMod (2^142719) 21 ((2^142719+1)/3) 70000 1) 700 = true by decide +kernel)

private theorem r71309_70701 : RangeCond 71309 71333 70701 71310 := by
  exact rangeCheck_sound (show rangeCheck 71309 71333 32 142719
    (70701) (powMod (2^142719) 21 ((2^142719+1)/3) 70700 1) 609 = true by decide +kernel)

theorem pairs71309 : AllPairs 71309 71333 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_1 (RangeCond.trans r71309_701 r71309_1401)) (RangeCond.trans r71309_2101 (RangeCond.trans r71309_2801 r71309_3501))) (RangeCond.trans (RangeCond.trans r71309_4201 (RangeCond.trans r71309_4901 r71309_5601)) (RangeCond.trans r71309_6301 (RangeCond.trans r71309_7001 r71309_7701)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_8401 (RangeCond.trans r71309_9101 r71309_9801)) (RangeCond.trans r71309_10501 (RangeCond.trans r71309_11201 r71309_11901))) (RangeCond.trans (RangeCond.trans r71309_12601 (RangeCond.trans r71309_13301 r71309_14001)) (RangeCond.trans (RangeCond.trans r71309_14701 r71309_15401) (RangeCond.trans r71309_16101 r71309_16801))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_17501 (RangeCond.trans r71309_18201 r71309_18901)) (RangeCond.trans r71309_19601 (RangeCond.trans r71309_20301 r71309_21001))) (RangeCond.trans (RangeCond.trans r71309_21701 (RangeCond.trans r71309_22401 r71309_23101)) (RangeCond.trans (RangeCond.trans r71309_23801 r71309_24501) (RangeCond.trans r71309_25201 r71309_25901)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_26601 (RangeCond.trans r71309_27301 r71309_28001)) (RangeCond.trans r71309_28701 (RangeCond.trans r71309_29401 r71309_30101))) (RangeCond.trans (RangeCond.trans r71309_30801 (RangeCond.trans r71309_31501 r71309_32201)) (RangeCond.trans (RangeCond.trans r71309_32901 r71309_33601) (RangeCond.trans r71309_34301 r71309_35001)))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_35701 (RangeCond.trans r71309_36401 r71309_37101)) (RangeCond.trans r71309_37801 (RangeCond.trans r71309_38501 r71309_39201))) (RangeCond.trans (RangeCond.trans r71309_39901 (RangeCond.trans r71309_40601 r71309_41301)) (RangeCond.trans r71309_42001 (RangeCond.trans r71309_42701 r71309_43401)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_44101 (RangeCond.trans r71309_44801 r71309_45501)) (RangeCond.trans r71309_46201 (RangeCond.trans r71309_46901 r71309_47601))) (RangeCond.trans (RangeCond.trans r71309_48301 (RangeCond.trans r71309_49001 r71309_49701)) (RangeCond.trans (RangeCond.trans r71309_50401 r71309_51101) (RangeCond.trans r71309_51801 r71309_52501))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_53201 (RangeCond.trans r71309_53901 r71309_54601)) (RangeCond.trans r71309_55301 (RangeCond.trans r71309_56001 r71309_56701))) (RangeCond.trans (RangeCond.trans r71309_57401 (RangeCond.trans r71309_58101 r71309_58801)) (RangeCond.trans (RangeCond.trans r71309_59501 r71309_60201) (RangeCond.trans r71309_60901 r71309_61601)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r71309_62301 (RangeCond.trans r71309_63001 r71309_63701)) (RangeCond.trans r71309_64401 (RangeCond.trans r71309_65101 r71309_65801))) (RangeCond.trans (RangeCond.trans r71309_66501 (RangeCond.trans r71309_67201 r71309_67901)) (RangeCond.trans (RangeCond.trans r71309_68601 r71309_69301) (RangeCond.trans r71309_70001 r71309_70701)))))))

#print axioms pairs71309

end Cycle108
