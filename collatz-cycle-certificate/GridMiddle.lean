import FastHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem r688_1 : RangeCond 688 712 1 689 := by
  exact rangeCheck_sound (show rangeCheck 688 712 32 1477
    (1) (powMod (2^1477) 21 ((2^1477+1)/3) 0 1) 688 = true by decide +kernel)

theorem pairs688 : AllPairs 688 712 := by
  apply allPairs_of_range
  exact r688_1

private theorem r1105_1 : RangeCond 1105 1129 1 701 := by
  exact rangeCheck_sound (show rangeCheck 1105 1129 32 2311
    (1) (powMod (2^2311) 21 ((2^2311+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r1105_701 : RangeCond 1105 1129 701 1106 := by
  exact rangeCheck_sound (show rangeCheck 1105 1129 32 2311
    (701) (powMod (2^2311) 21 ((2^2311+1)/3) 700 1) 405 = true by decide +kernel)

theorem pairs1105 : AllPairs 1105 1129 := by
  apply allPairs_of_range
  exact (RangeCond.trans r1105_1 r1105_701)

private theorem r1766_1 : RangeCond 1766 1790 1 701 := by
  exact rangeCheck_sound (show rangeCheck 1766 1790 32 3633
    (1) (powMod (2^3633) 21 ((2^3633+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r1766_701 : RangeCond 1766 1790 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 1766 1790 32 3633
    (701) (powMod (2^3633) 21 ((2^3633+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r1766_1401 : RangeCond 1766 1790 1401 1767 := by
  exact rangeCheck_sound (show rangeCheck 1766 1790 32 3633
    (1401) (powMod (2^3633) 21 ((2^3633+1)/3) 1400 1) 366 = true by decide +kernel)

theorem pairs1766 : AllPairs 1766 1790 := by
  apply allPairs_of_range
  exact (RangeCond.trans r1766_1 (RangeCond.trans r1766_701 r1766_1401))

private theorem r2814_1 : RangeCond 2814 2838 1 701 := by
  exact rangeCheck_sound (show rangeCheck 2814 2838 32 5729
    (1) (powMod (2^5729) 21 ((2^5729+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r2814_701 : RangeCond 2814 2838 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 2814 2838 32 5729
    (701) (powMod (2^5729) 21 ((2^5729+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r2814_1401 : RangeCond 2814 2838 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 2814 2838 32 5729
    (1401) (powMod (2^5729) 21 ((2^5729+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r2814_2101 : RangeCond 2814 2838 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 2814 2838 32 5729
    (2101) (powMod (2^5729) 21 ((2^5729+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r2814_2801 : RangeCond 2814 2838 2801 2815 := by
  exact rangeCheck_sound (show rangeCheck 2814 2838 32 5729
    (2801) (powMod (2^5729) 21 ((2^5729+1)/3) 2800 1) 14 = true by decide +kernel)

theorem pairs2814 : AllPairs 2814 2838 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans r2814_1 r2814_701) (RangeCond.trans r2814_1401 (RangeCond.trans r2814_2101 r2814_2801)))

private theorem r4475_1 : RangeCond 4475 4499 1 701 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (1) (powMod (2^9051) 21 ((2^9051+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r4475_701 : RangeCond 4475 4499 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (701) (powMod (2^9051) 21 ((2^9051+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r4475_1401 : RangeCond 4475 4499 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (1401) (powMod (2^9051) 21 ((2^9051+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r4475_2101 : RangeCond 4475 4499 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (2101) (powMod (2^9051) 21 ((2^9051+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r4475_2801 : RangeCond 4475 4499 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (2801) (powMod (2^9051) 21 ((2^9051+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r4475_3501 : RangeCond 4475 4499 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (3501) (powMod (2^9051) 21 ((2^9051+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r4475_4201 : RangeCond 4475 4499 4201 4476 := by
  exact rangeCheck_sound (show rangeCheck 4475 4499 32 9051
    (4201) (powMod (2^9051) 21 ((2^9051+1)/3) 4200 1) 275 = true by decide +kernel)

theorem pairs4475 : AllPairs 4475 4499 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans r4475_1 (RangeCond.trans r4475_701 r4475_1401)) (RangeCond.trans (RangeCond.trans r4475_2101 r4475_2801) (RangeCond.trans r4475_3501 r4475_4201)))

private theorem r7107_1 : RangeCond 7107 7131 1 701 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (1) (powMod (2^14315) 21 ((2^14315+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r7107_701 : RangeCond 7107 7131 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (701) (powMod (2^14315) 21 ((2^14315+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r7107_1401 : RangeCond 7107 7131 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (1401) (powMod (2^14315) 21 ((2^14315+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r7107_2101 : RangeCond 7107 7131 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (2101) (powMod (2^14315) 21 ((2^14315+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r7107_2801 : RangeCond 7107 7131 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (2801) (powMod (2^14315) 21 ((2^14315+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r7107_3501 : RangeCond 7107 7131 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (3501) (powMod (2^14315) 21 ((2^14315+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r7107_4201 : RangeCond 7107 7131 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (4201) (powMod (2^14315) 21 ((2^14315+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r7107_4901 : RangeCond 7107 7131 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (4901) (powMod (2^14315) 21 ((2^14315+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r7107_5601 : RangeCond 7107 7131 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (5601) (powMod (2^14315) 21 ((2^14315+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r7107_6301 : RangeCond 7107 7131 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (6301) (powMod (2^14315) 21 ((2^14315+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r7107_7001 : RangeCond 7107 7131 7001 7108 := by
  exact rangeCheck_sound (show rangeCheck 7107 7131 32 14315
    (7001) (powMod (2^14315) 21 ((2^14315+1)/3) 7000 1) 107 = true by decide +kernel)

theorem pairs7107 : AllPairs 7107 7131 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans r7107_1 r7107_701) (RangeCond.trans r7107_1401 (RangeCond.trans r7107_2101 r7107_2801))) (RangeCond.trans (RangeCond.trans r7107_3501 (RangeCond.trans r7107_4201 r7107_4901)) (RangeCond.trans r7107_5601 (RangeCond.trans r7107_6301 r7107_7001))))

private theorem r11279_1 : RangeCond 11279 11303 1 701 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (1) (powMod (2^22659) 21 ((2^22659+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r11279_701 : RangeCond 11279 11303 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (701) (powMod (2^22659) 21 ((2^22659+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r11279_1401 : RangeCond 11279 11303 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (1401) (powMod (2^22659) 21 ((2^22659+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r11279_2101 : RangeCond 11279 11303 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (2101) (powMod (2^22659) 21 ((2^22659+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r11279_2801 : RangeCond 11279 11303 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (2801) (powMod (2^22659) 21 ((2^22659+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r11279_3501 : RangeCond 11279 11303 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (3501) (powMod (2^22659) 21 ((2^22659+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r11279_4201 : RangeCond 11279 11303 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (4201) (powMod (2^22659) 21 ((2^22659+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r11279_4901 : RangeCond 11279 11303 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (4901) (powMod (2^22659) 21 ((2^22659+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r11279_5601 : RangeCond 11279 11303 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (5601) (powMod (2^22659) 21 ((2^22659+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r11279_6301 : RangeCond 11279 11303 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (6301) (powMod (2^22659) 21 ((2^22659+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r11279_7001 : RangeCond 11279 11303 7001 7701 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (7001) (powMod (2^22659) 21 ((2^22659+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r11279_7701 : RangeCond 11279 11303 7701 8401 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (7701) (powMod (2^22659) 21 ((2^22659+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r11279_8401 : RangeCond 11279 11303 8401 9101 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (8401) (powMod (2^22659) 21 ((2^22659+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r11279_9101 : RangeCond 11279 11303 9101 9801 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (9101) (powMod (2^22659) 21 ((2^22659+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r11279_9801 : RangeCond 11279 11303 9801 10501 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (9801) (powMod (2^22659) 21 ((2^22659+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r11279_10501 : RangeCond 11279 11303 10501 11201 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (10501) (powMod (2^22659) 21 ((2^22659+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r11279_11201 : RangeCond 11279 11303 11201 11280 := by
  exact rangeCheck_sound (show rangeCheck 11279 11303 32 22659
    (11201) (powMod (2^22659) 21 ((2^22659+1)/3) 11200 1) 79 = true by decide +kernel)

theorem pairs11279 : AllPairs 11279 11303 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r11279_1 r11279_701) (RangeCond.trans r11279_1401 r11279_2101)) (RangeCond.trans (RangeCond.trans r11279_2801 r11279_3501) (RangeCond.trans r11279_4201 r11279_4901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r11279_5601 r11279_6301) (RangeCond.trans r11279_7001 r11279_7701)) (RangeCond.trans (RangeCond.trans r11279_8401 r11279_9101) (RangeCond.trans r11279_9801 (RangeCond.trans r11279_10501 r11279_11201)))))

private theorem r17891_1 : RangeCond 17891 17915 1 701 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (1) (powMod (2^35883) 21 ((2^35883+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r17891_701 : RangeCond 17891 17915 701 1401 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (701) (powMod (2^35883) 21 ((2^35883+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r17891_1401 : RangeCond 17891 17915 1401 2101 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (1401) (powMod (2^35883) 21 ((2^35883+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r17891_2101 : RangeCond 17891 17915 2101 2801 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (2101) (powMod (2^35883) 21 ((2^35883+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r17891_2801 : RangeCond 17891 17915 2801 3501 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (2801) (powMod (2^35883) 21 ((2^35883+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r17891_3501 : RangeCond 17891 17915 3501 4201 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (3501) (powMod (2^35883) 21 ((2^35883+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r17891_4201 : RangeCond 17891 17915 4201 4901 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (4201) (powMod (2^35883) 21 ((2^35883+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r17891_4901 : RangeCond 17891 17915 4901 5601 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (4901) (powMod (2^35883) 21 ((2^35883+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r17891_5601 : RangeCond 17891 17915 5601 6301 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (5601) (powMod (2^35883) 21 ((2^35883+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r17891_6301 : RangeCond 17891 17915 6301 7001 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (6301) (powMod (2^35883) 21 ((2^35883+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r17891_7001 : RangeCond 17891 17915 7001 7701 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (7001) (powMod (2^35883) 21 ((2^35883+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r17891_7701 : RangeCond 17891 17915 7701 8401 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (7701) (powMod (2^35883) 21 ((2^35883+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r17891_8401 : RangeCond 17891 17915 8401 9101 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (8401) (powMod (2^35883) 21 ((2^35883+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r17891_9101 : RangeCond 17891 17915 9101 9801 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (9101) (powMod (2^35883) 21 ((2^35883+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r17891_9801 : RangeCond 17891 17915 9801 10501 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (9801) (powMod (2^35883) 21 ((2^35883+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r17891_10501 : RangeCond 17891 17915 10501 11201 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (10501) (powMod (2^35883) 21 ((2^35883+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r17891_11201 : RangeCond 17891 17915 11201 11901 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (11201) (powMod (2^35883) 21 ((2^35883+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r17891_11901 : RangeCond 17891 17915 11901 12601 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (11901) (powMod (2^35883) 21 ((2^35883+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r17891_12601 : RangeCond 17891 17915 12601 13301 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (12601) (powMod (2^35883) 21 ((2^35883+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r17891_13301 : RangeCond 17891 17915 13301 14001 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (13301) (powMod (2^35883) 21 ((2^35883+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r17891_14001 : RangeCond 17891 17915 14001 14701 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (14001) (powMod (2^35883) 21 ((2^35883+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r17891_14701 : RangeCond 17891 17915 14701 15401 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (14701) (powMod (2^35883) 21 ((2^35883+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r17891_15401 : RangeCond 17891 17915 15401 16101 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (15401) (powMod (2^35883) 21 ((2^35883+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r17891_16101 : RangeCond 17891 17915 16101 16801 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (16101) (powMod (2^35883) 21 ((2^35883+1)/3) 16100 1) 700 = true by decide +kernel)

private theorem r17891_16801 : RangeCond 17891 17915 16801 17501 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (16801) (powMod (2^35883) 21 ((2^35883+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r17891_17501 : RangeCond 17891 17915 17501 17892 := by
  exact rangeCheck_sound (show rangeCheck 17891 17915 32 35883
    (17501) (powMod (2^35883) 21 ((2^35883+1)/3) 17500 1) 391 = true by decide +kernel)

theorem pairs17891 : AllPairs 17891 17915 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r17891_1 (RangeCond.trans r17891_701 r17891_1401)) (RangeCond.trans r17891_2101 (RangeCond.trans r17891_2801 r17891_3501))) (RangeCond.trans (RangeCond.trans r17891_4201 (RangeCond.trans r17891_4901 r17891_5601)) (RangeCond.trans (RangeCond.trans r17891_6301 r17891_7001) (RangeCond.trans r17891_7701 r17891_8401)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r17891_9101 (RangeCond.trans r17891_9801 r17891_10501)) (RangeCond.trans r17891_11201 (RangeCond.trans r17891_11901 r17891_12601))) (RangeCond.trans (RangeCond.trans r17891_13301 (RangeCond.trans r17891_14001 r17891_14701)) (RangeCond.trans (RangeCond.trans r17891_15401 r17891_16101) (RangeCond.trans r17891_16801 r17891_17501)))))

#print axioms pairs17891

end Cycle108
