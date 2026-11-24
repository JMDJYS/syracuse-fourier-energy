import ReducedHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem r179174_1 : RangeCond 179174 179198 1 701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 358449
    (1) (powMod (2^358449) 21 ((2^358449+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r179174_701 : RangeCond 179174 179198 701 1401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 357049
    (701) (powMod (2^357049) 21 ((2^357049+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r179174_1401 : RangeCond 179174 179198 1401 2101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 355649
    (1401) (powMod (2^355649) 21 ((2^355649+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r179174_2101 : RangeCond 179174 179198 2101 2801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 354249
    (2101) (powMod (2^354249) 21 ((2^354249+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r179174_2801 : RangeCond 179174 179198 2801 3501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 352849
    (2801) (powMod (2^352849) 21 ((2^352849+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r179174_3501 : RangeCond 179174 179198 3501 4201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 351449
    (3501) (powMod (2^351449) 21 ((2^351449+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r179174_4201 : RangeCond 179174 179198 4201 4901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 350049
    (4201) (powMod (2^350049) 21 ((2^350049+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r179174_4901 : RangeCond 179174 179198 4901 5601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 348649
    (4901) (powMod (2^348649) 21 ((2^348649+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r179174_5601 : RangeCond 179174 179198 5601 6301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 347249
    (5601) (powMod (2^347249) 21 ((2^347249+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r179174_6301 : RangeCond 179174 179198 6301 7001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 345849
    (6301) (powMod (2^345849) 21 ((2^345849+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r179174_7001 : RangeCond 179174 179198 7001 7701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 344449
    (7001) (powMod (2^344449) 21 ((2^344449+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r179174_7701 : RangeCond 179174 179198 7701 8401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 343049
    (7701) (powMod (2^343049) 21 ((2^343049+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r179174_8401 : RangeCond 179174 179198 8401 9101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 341649
    (8401) (powMod (2^341649) 21 ((2^341649+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r179174_9101 : RangeCond 179174 179198 9101 9801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 340249
    (9101) (powMod (2^340249) 21 ((2^340249+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r179174_9801 : RangeCond 179174 179198 9801 10501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 338849
    (9801) (powMod (2^338849) 21 ((2^338849+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r179174_10501 : RangeCond 179174 179198 10501 11201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 337449
    (10501) (powMod (2^337449) 21 ((2^337449+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r179174_11201 : RangeCond 179174 179198 11201 11901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 336049
    (11201) (powMod (2^336049) 21 ((2^336049+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r179174_11901 : RangeCond 179174 179198 11901 12601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 334649
    (11901) (powMod (2^334649) 21 ((2^334649+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r179174_12601 : RangeCond 179174 179198 12601 13301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 333249
    (12601) (powMod (2^333249) 21 ((2^333249+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r179174_13301 : RangeCond 179174 179198 13301 14001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 331849
    (13301) (powMod (2^331849) 21 ((2^331849+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r179174_14001 : RangeCond 179174 179198 14001 14701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 330449
    (14001) (powMod (2^330449) 21 ((2^330449+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r179174_14701 : RangeCond 179174 179198 14701 15401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 329049
    (14701) (powMod (2^329049) 21 ((2^329049+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r179174_15401 : RangeCond 179174 179198 15401 16101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 327649
    (15401) (powMod (2^327649) 21 ((2^327649+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r179174_16101 : RangeCond 179174 179198 16101 16801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 326249
    (16101) (powMod (2^326249) 21 ((2^326249+1)/3) 16100 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 16800"

private theorem r179174_16801 : RangeCond 179174 179198 16801 17501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 324849
    (16801) (powMod (2^324849) 21 ((2^324849+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r179174_17501 : RangeCond 179174 179198 17501 18201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 323449
    (17501) (powMod (2^323449) 21 ((2^323449+1)/3) 17500 1) 700 = true by decide +kernel)

private theorem r179174_18201 : RangeCond 179174 179198 18201 18901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 322049
    (18201) (powMod (2^322049) 21 ((2^322049+1)/3) 18200 1) 700 = true by decide +kernel)

private theorem r179174_18901 : RangeCond 179174 179198 18901 19601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 320649
    (18901) (powMod (2^320649) 21 ((2^320649+1)/3) 18900 1) 700 = true by decide +kernel)

private theorem r179174_19601 : RangeCond 179174 179198 19601 20301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 319249
    (19601) (powMod (2^319249) 21 ((2^319249+1)/3) 19600 1) 700 = true by decide +kernel)

private theorem r179174_20301 : RangeCond 179174 179198 20301 21001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 317849
    (20301) (powMod (2^317849) 21 ((2^317849+1)/3) 20300 1) 700 = true by decide +kernel)

private theorem r179174_21001 : RangeCond 179174 179198 21001 21701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 316449
    (21001) (powMod (2^316449) 21 ((2^316449+1)/3) 21000 1) 700 = true by decide +kernel)

private theorem r179174_21701 : RangeCond 179174 179198 21701 22401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 315049
    (21701) (powMod (2^315049) 21 ((2^315049+1)/3) 21700 1) 700 = true by decide +kernel)

private theorem r179174_22401 : RangeCond 179174 179198 22401 23101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 313649
    (22401) (powMod (2^313649) 21 ((2^313649+1)/3) 22400 1) 700 = true by decide +kernel)

private theorem r179174_23101 : RangeCond 179174 179198 23101 23801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 312249
    (23101) (powMod (2^312249) 21 ((2^312249+1)/3) 23100 1) 700 = true by decide +kernel)

private theorem r179174_23801 : RangeCond 179174 179198 23801 24501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 310849
    (23801) (powMod (2^310849) 21 ((2^310849+1)/3) 23800 1) 700 = true by decide +kernel)

private theorem r179174_24501 : RangeCond 179174 179198 24501 25201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 309449
    (24501) (powMod (2^309449) 21 ((2^309449+1)/3) 24500 1) 700 = true by decide +kernel)

private theorem r179174_25201 : RangeCond 179174 179198 25201 25901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 308049
    (25201) (powMod (2^308049) 21 ((2^308049+1)/3) 25200 1) 700 = true by decide +kernel)

private theorem r179174_25901 : RangeCond 179174 179198 25901 26601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 306649
    (25901) (powMod (2^306649) 21 ((2^306649+1)/3) 25900 1) 700 = true by decide +kernel)

private theorem r179174_26601 : RangeCond 179174 179198 26601 27301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 305249
    (26601) (powMod (2^305249) 21 ((2^305249+1)/3) 26600 1) 700 = true by decide +kernel)

private theorem r179174_27301 : RangeCond 179174 179198 27301 28001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 303849
    (27301) (powMod (2^303849) 21 ((2^303849+1)/3) 27300 1) 700 = true by decide +kernel)

private theorem r179174_28001 : RangeCond 179174 179198 28001 28701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 302449
    (28001) (powMod (2^302449) 21 ((2^302449+1)/3) 28000 1) 700 = true by decide +kernel)

private theorem r179174_28701 : RangeCond 179174 179198 28701 29401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 301049
    (28701) (powMod (2^301049) 21 ((2^301049+1)/3) 28700 1) 700 = true by decide +kernel)

private theorem r179174_29401 : RangeCond 179174 179198 29401 30101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 299649
    (29401) (powMod (2^299649) 21 ((2^299649+1)/3) 29400 1) 700 = true by decide +kernel)

private theorem r179174_30101 : RangeCond 179174 179198 30101 30801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 298249
    (30101) (powMod (2^298249) 21 ((2^298249+1)/3) 30100 1) 700 = true by decide +kernel)

private theorem r179174_30801 : RangeCond 179174 179198 30801 31501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 296849
    (30801) (powMod (2^296849) 21 ((2^296849+1)/3) 30800 1) 700 = true by decide +kernel)

private theorem r179174_31501 : RangeCond 179174 179198 31501 32201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 295449
    (31501) (powMod (2^295449) 21 ((2^295449+1)/3) 31500 1) 700 = true by decide +kernel)

private theorem r179174_32201 : RangeCond 179174 179198 32201 32901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 294049
    (32201) (powMod (2^294049) 21 ((2^294049+1)/3) 32200 1) 700 = true by decide +kernel)

private theorem r179174_32901 : RangeCond 179174 179198 32901 33601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 292649
    (32901) (powMod (2^292649) 21 ((2^292649+1)/3) 32900 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 33600"

private theorem r179174_33601 : RangeCond 179174 179198 33601 34301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 291249
    (33601) (powMod (2^291249) 21 ((2^291249+1)/3) 33600 1) 700 = true by decide +kernel)

private theorem r179174_34301 : RangeCond 179174 179198 34301 35001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 289849
    (34301) (powMod (2^289849) 21 ((2^289849+1)/3) 34300 1) 700 = true by decide +kernel)

private theorem r179174_35001 : RangeCond 179174 179198 35001 35701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 288449
    (35001) (powMod (2^288449) 21 ((2^288449+1)/3) 35000 1) 700 = true by decide +kernel)

private theorem r179174_35701 : RangeCond 179174 179198 35701 36401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 287049
    (35701) (powMod (2^287049) 21 ((2^287049+1)/3) 35700 1) 700 = true by decide +kernel)

private theorem r179174_36401 : RangeCond 179174 179198 36401 37101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 285649
    (36401) (powMod (2^285649) 21 ((2^285649+1)/3) 36400 1) 700 = true by decide +kernel)

private theorem r179174_37101 : RangeCond 179174 179198 37101 37801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 284249
    (37101) (powMod (2^284249) 21 ((2^284249+1)/3) 37100 1) 700 = true by decide +kernel)

private theorem r179174_37801 : RangeCond 179174 179198 37801 38501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 282849
    (37801) (powMod (2^282849) 21 ((2^282849+1)/3) 37800 1) 700 = true by decide +kernel)

private theorem r179174_38501 : RangeCond 179174 179198 38501 39201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 281449
    (38501) (powMod (2^281449) 21 ((2^281449+1)/3) 38500 1) 700 = true by decide +kernel)

private theorem r179174_39201 : RangeCond 179174 179198 39201 39901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 280049
    (39201) (powMod (2^280049) 21 ((2^280049+1)/3) 39200 1) 700 = true by decide +kernel)

private theorem r179174_39901 : RangeCond 179174 179198 39901 40601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 278649
    (39901) (powMod (2^278649) 21 ((2^278649+1)/3) 39900 1) 700 = true by decide +kernel)

private theorem r179174_40601 : RangeCond 179174 179198 40601 41301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 277249
    (40601) (powMod (2^277249) 21 ((2^277249+1)/3) 40600 1) 700 = true by decide +kernel)

private theorem r179174_41301 : RangeCond 179174 179198 41301 42001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 275849
    (41301) (powMod (2^275849) 21 ((2^275849+1)/3) 41300 1) 700 = true by decide +kernel)

private theorem r179174_42001 : RangeCond 179174 179198 42001 42701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 274449
    (42001) (powMod (2^274449) 21 ((2^274449+1)/3) 42000 1) 700 = true by decide +kernel)

private theorem r179174_42701 : RangeCond 179174 179198 42701 43401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 273049
    (42701) (powMod (2^273049) 21 ((2^273049+1)/3) 42700 1) 700 = true by decide +kernel)

private theorem r179174_43401 : RangeCond 179174 179198 43401 44101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 271649
    (43401) (powMod (2^271649) 21 ((2^271649+1)/3) 43400 1) 700 = true by decide +kernel)

private theorem r179174_44101 : RangeCond 179174 179198 44101 44801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 270249
    (44101) (powMod (2^270249) 21 ((2^270249+1)/3) 44100 1) 700 = true by decide +kernel)

private theorem r179174_44801 : RangeCond 179174 179198 44801 45501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 268849
    (44801) (powMod (2^268849) 21 ((2^268849+1)/3) 44800 1) 700 = true by decide +kernel)

private theorem r179174_45501 : RangeCond 179174 179198 45501 46201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 267449
    (45501) (powMod (2^267449) 21 ((2^267449+1)/3) 45500 1) 700 = true by decide +kernel)

private theorem r179174_46201 : RangeCond 179174 179198 46201 46901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 266049
    (46201) (powMod (2^266049) 21 ((2^266049+1)/3) 46200 1) 700 = true by decide +kernel)

private theorem r179174_46901 : RangeCond 179174 179198 46901 47601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 264649
    (46901) (powMod (2^264649) 21 ((2^264649+1)/3) 46900 1) 700 = true by decide +kernel)

private theorem r179174_47601 : RangeCond 179174 179198 47601 48301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 263249
    (47601) (powMod (2^263249) 21 ((2^263249+1)/3) 47600 1) 700 = true by decide +kernel)

private theorem r179174_48301 : RangeCond 179174 179198 48301 49001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 261849
    (48301) (powMod (2^261849) 21 ((2^261849+1)/3) 48300 1) 700 = true by decide +kernel)

private theorem r179174_49001 : RangeCond 179174 179198 49001 49701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 260449
    (49001) (powMod (2^260449) 21 ((2^260449+1)/3) 49000 1) 700 = true by decide +kernel)

private theorem r179174_49701 : RangeCond 179174 179198 49701 50401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 259049
    (49701) (powMod (2^259049) 21 ((2^259049+1)/3) 49700 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 50400"

private theorem r179174_50401 : RangeCond 179174 179198 50401 51101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 257649
    (50401) (powMod (2^257649) 21 ((2^257649+1)/3) 50400 1) 700 = true by decide +kernel)

private theorem r179174_51101 : RangeCond 179174 179198 51101 51801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 256249
    (51101) (powMod (2^256249) 21 ((2^256249+1)/3) 51100 1) 700 = true by decide +kernel)

private theorem r179174_51801 : RangeCond 179174 179198 51801 52501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 254849
    (51801) (powMod (2^254849) 21 ((2^254849+1)/3) 51800 1) 700 = true by decide +kernel)

private theorem r179174_52501 : RangeCond 179174 179198 52501 53201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 253449
    (52501) (powMod (2^253449) 21 ((2^253449+1)/3) 52500 1) 700 = true by decide +kernel)

private theorem r179174_53201 : RangeCond 179174 179198 53201 53901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 252049
    (53201) (powMod (2^252049) 21 ((2^252049+1)/3) 53200 1) 700 = true by decide +kernel)

private theorem r179174_53901 : RangeCond 179174 179198 53901 54601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 250649
    (53901) (powMod (2^250649) 21 ((2^250649+1)/3) 53900 1) 700 = true by decide +kernel)

private theorem r179174_54601 : RangeCond 179174 179198 54601 55301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 249249
    (54601) (powMod (2^249249) 21 ((2^249249+1)/3) 54600 1) 700 = true by decide +kernel)

private theorem r179174_55301 : RangeCond 179174 179198 55301 56001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 247849
    (55301) (powMod (2^247849) 21 ((2^247849+1)/3) 55300 1) 700 = true by decide +kernel)

private theorem r179174_56001 : RangeCond 179174 179198 56001 56701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 246449
    (56001) (powMod (2^246449) 21 ((2^246449+1)/3) 56000 1) 700 = true by decide +kernel)

private theorem r179174_56701 : RangeCond 179174 179198 56701 57401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 245049
    (56701) (powMod (2^245049) 21 ((2^245049+1)/3) 56700 1) 700 = true by decide +kernel)

private theorem r179174_57401 : RangeCond 179174 179198 57401 58101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 243649
    (57401) (powMod (2^243649) 21 ((2^243649+1)/3) 57400 1) 700 = true by decide +kernel)

private theorem r179174_58101 : RangeCond 179174 179198 58101 58801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 242249
    (58101) (powMod (2^242249) 21 ((2^242249+1)/3) 58100 1) 700 = true by decide +kernel)

private theorem r179174_58801 : RangeCond 179174 179198 58801 59501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 240849
    (58801) (powMod (2^240849) 21 ((2^240849+1)/3) 58800 1) 700 = true by decide +kernel)

private theorem r179174_59501 : RangeCond 179174 179198 59501 60201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 239449
    (59501) (powMod (2^239449) 21 ((2^239449+1)/3) 59500 1) 700 = true by decide +kernel)

private theorem r179174_60201 : RangeCond 179174 179198 60201 60901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 238049
    (60201) (powMod (2^238049) 21 ((2^238049+1)/3) 60200 1) 700 = true by decide +kernel)

private theorem r179174_60901 : RangeCond 179174 179198 60901 61601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 236649
    (60901) (powMod (2^236649) 21 ((2^236649+1)/3) 60900 1) 700 = true by decide +kernel)

private theorem r179174_61601 : RangeCond 179174 179198 61601 62301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 235249
    (61601) (powMod (2^235249) 21 ((2^235249+1)/3) 61600 1) 700 = true by decide +kernel)

private theorem r179174_62301 : RangeCond 179174 179198 62301 63001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 233849
    (62301) (powMod (2^233849) 21 ((2^233849+1)/3) 62300 1) 700 = true by decide +kernel)

private theorem r179174_63001 : RangeCond 179174 179198 63001 63701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 232449
    (63001) (powMod (2^232449) 21 ((2^232449+1)/3) 63000 1) 700 = true by decide +kernel)

private theorem r179174_63701 : RangeCond 179174 179198 63701 64401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 231049
    (63701) (powMod (2^231049) 21 ((2^231049+1)/3) 63700 1) 700 = true by decide +kernel)

private theorem r179174_64401 : RangeCond 179174 179198 64401 65101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 229649
    (64401) (powMod (2^229649) 21 ((2^229649+1)/3) 64400 1) 700 = true by decide +kernel)

private theorem r179174_65101 : RangeCond 179174 179198 65101 65801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 228249
    (65101) (powMod (2^228249) 21 ((2^228249+1)/3) 65100 1) 700 = true by decide +kernel)

private theorem r179174_65801 : RangeCond 179174 179198 65801 66501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 226849
    (65801) (powMod (2^226849) 21 ((2^226849+1)/3) 65800 1) 700 = true by decide +kernel)

private theorem r179174_66501 : RangeCond 179174 179198 66501 67201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 225449
    (66501) (powMod (2^225449) 21 ((2^225449+1)/3) 66500 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 67200"

private theorem r179174_67201 : RangeCond 179174 179198 67201 67901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 224049
    (67201) (powMod (2^224049) 21 ((2^224049+1)/3) 67200 1) 700 = true by decide +kernel)

private theorem r179174_67901 : RangeCond 179174 179198 67901 68601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 222649
    (67901) (powMod (2^222649) 21 ((2^222649+1)/3) 67900 1) 700 = true by decide +kernel)

private theorem r179174_68601 : RangeCond 179174 179198 68601 69301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 221249
    (68601) (powMod (2^221249) 21 ((2^221249+1)/3) 68600 1) 700 = true by decide +kernel)

private theorem r179174_69301 : RangeCond 179174 179198 69301 70001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 219849
    (69301) (powMod (2^219849) 21 ((2^219849+1)/3) 69300 1) 700 = true by decide +kernel)

private theorem r179174_70001 : RangeCond 179174 179198 70001 70701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 218449
    (70001) (powMod (2^218449) 21 ((2^218449+1)/3) 70000 1) 700 = true by decide +kernel)

private theorem r179174_70701 : RangeCond 179174 179198 70701 71401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 217049
    (70701) (powMod (2^217049) 21 ((2^217049+1)/3) 70700 1) 700 = true by decide +kernel)

private theorem r179174_71401 : RangeCond 179174 179198 71401 72101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 215649
    (71401) (powMod (2^215649) 21 ((2^215649+1)/3) 71400 1) 700 = true by decide +kernel)

private theorem r179174_72101 : RangeCond 179174 179198 72101 72801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 214249
    (72101) (powMod (2^214249) 21 ((2^214249+1)/3) 72100 1) 700 = true by decide +kernel)

private theorem r179174_72801 : RangeCond 179174 179198 72801 73501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 212849
    (72801) (powMod (2^212849) 21 ((2^212849+1)/3) 72800 1) 700 = true by decide +kernel)

private theorem r179174_73501 : RangeCond 179174 179198 73501 74201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 211449
    (73501) (powMod (2^211449) 21 ((2^211449+1)/3) 73500 1) 700 = true by decide +kernel)

private theorem r179174_74201 : RangeCond 179174 179198 74201 74901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 210049
    (74201) (powMod (2^210049) 21 ((2^210049+1)/3) 74200 1) 700 = true by decide +kernel)

private theorem r179174_74901 : RangeCond 179174 179198 74901 75601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 208649
    (74901) (powMod (2^208649) 21 ((2^208649+1)/3) 74900 1) 700 = true by decide +kernel)

private theorem r179174_75601 : RangeCond 179174 179198 75601 76301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 207249
    (75601) (powMod (2^207249) 21 ((2^207249+1)/3) 75600 1) 700 = true by decide +kernel)

private theorem r179174_76301 : RangeCond 179174 179198 76301 77001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 205849
    (76301) (powMod (2^205849) 21 ((2^205849+1)/3) 76300 1) 700 = true by decide +kernel)

private theorem r179174_77001 : RangeCond 179174 179198 77001 77701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 204449
    (77001) (powMod (2^204449) 21 ((2^204449+1)/3) 77000 1) 700 = true by decide +kernel)

private theorem r179174_77701 : RangeCond 179174 179198 77701 78401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 203049
    (77701) (powMod (2^203049) 21 ((2^203049+1)/3) 77700 1) 700 = true by decide +kernel)

private theorem r179174_78401 : RangeCond 179174 179198 78401 79101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 201649
    (78401) (powMod (2^201649) 21 ((2^201649+1)/3) 78400 1) 700 = true by decide +kernel)

private theorem r179174_79101 : RangeCond 179174 179198 79101 79801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 200249
    (79101) (powMod (2^200249) 21 ((2^200249+1)/3) 79100 1) 700 = true by decide +kernel)

private theorem r179174_79801 : RangeCond 179174 179198 79801 80501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 198849
    (79801) (powMod (2^198849) 21 ((2^198849+1)/3) 79800 1) 700 = true by decide +kernel)

private theorem r179174_80501 : RangeCond 179174 179198 80501 81201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 197449
    (80501) (powMod (2^197449) 21 ((2^197449+1)/3) 80500 1) 700 = true by decide +kernel)

private theorem r179174_81201 : RangeCond 179174 179198 81201 81901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 196049
    (81201) (powMod (2^196049) 21 ((2^196049+1)/3) 81200 1) 700 = true by decide +kernel)

private theorem r179174_81901 : RangeCond 179174 179198 81901 82601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 194649
    (81901) (powMod (2^194649) 21 ((2^194649+1)/3) 81900 1) 700 = true by decide +kernel)

private theorem r179174_82601 : RangeCond 179174 179198 82601 83301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 193249
    (82601) (powMod (2^193249) 21 ((2^193249+1)/3) 82600 1) 700 = true by decide +kernel)

private theorem r179174_83301 : RangeCond 179174 179198 83301 84001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 191849
    (83301) (powMod (2^191849) 21 ((2^191849+1)/3) 83300 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 84000"

private theorem r179174_84001 : RangeCond 179174 179198 84001 84701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 190449
    (84001) (powMod (2^190449) 21 ((2^190449+1)/3) 84000 1) 700 = true by decide +kernel)

private theorem r179174_84701 : RangeCond 179174 179198 84701 85401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 189049
    (84701) (powMod (2^189049) 21 ((2^189049+1)/3) 84700 1) 700 = true by decide +kernel)

private theorem r179174_85401 : RangeCond 179174 179198 85401 86101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 187649
    (85401) (powMod (2^187649) 21 ((2^187649+1)/3) 85400 1) 700 = true by decide +kernel)

private theorem r179174_86101 : RangeCond 179174 179198 86101 86801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 186249
    (86101) (powMod (2^186249) 21 ((2^186249+1)/3) 86100 1) 700 = true by decide +kernel)

private theorem r179174_86801 : RangeCond 179174 179198 86801 87501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 184849
    (86801) (powMod (2^184849) 21 ((2^184849+1)/3) 86800 1) 700 = true by decide +kernel)

private theorem r179174_87501 : RangeCond 179174 179198 87501 88201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 183449
    (87501) (powMod (2^183449) 21 ((2^183449+1)/3) 87500 1) 700 = true by decide +kernel)

private theorem r179174_88201 : RangeCond 179174 179198 88201 88901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 182049
    (88201) (powMod (2^182049) 21 ((2^182049+1)/3) 88200 1) 700 = true by decide +kernel)

private theorem r179174_88901 : RangeCond 179174 179198 88901 89601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 180649
    (88901) (powMod (2^180649) 21 ((2^180649+1)/3) 88900 1) 700 = true by decide +kernel)

private theorem r179174_89601 : RangeCond 179174 179198 89601 90301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 179249
    (89601) (powMod (2^179249) 21 ((2^179249+1)/3) 89600 1) 700 = true by decide +kernel)

private theorem r179174_90301 : RangeCond 179174 179198 90301 91001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 177849
    (90301) (powMod (2^177849) 21 ((2^177849+1)/3) 90300 1) 700 = true by decide +kernel)

private theorem r179174_91001 : RangeCond 179174 179198 91001 91701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 176449
    (91001) (powMod (2^176449) 21 ((2^176449+1)/3) 91000 1) 700 = true by decide +kernel)

private theorem r179174_91701 : RangeCond 179174 179198 91701 92401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 175049
    (91701) (powMod (2^175049) 21 ((2^175049+1)/3) 91700 1) 700 = true by decide +kernel)

private theorem r179174_92401 : RangeCond 179174 179198 92401 93101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 173649
    (92401) (powMod (2^173649) 21 ((2^173649+1)/3) 92400 1) 700 = true by decide +kernel)

private theorem r179174_93101 : RangeCond 179174 179198 93101 93801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 172249
    (93101) (powMod (2^172249) 21 ((2^172249+1)/3) 93100 1) 700 = true by decide +kernel)

private theorem r179174_93801 : RangeCond 179174 179198 93801 94501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 170849
    (93801) (powMod (2^170849) 21 ((2^170849+1)/3) 93800 1) 700 = true by decide +kernel)

private theorem r179174_94501 : RangeCond 179174 179198 94501 95201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 169449
    (94501) (powMod (2^169449) 21 ((2^169449+1)/3) 94500 1) 700 = true by decide +kernel)

private theorem r179174_95201 : RangeCond 179174 179198 95201 95901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 168049
    (95201) (powMod (2^168049) 21 ((2^168049+1)/3) 95200 1) 700 = true by decide +kernel)

private theorem r179174_95901 : RangeCond 179174 179198 95901 96601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 166649
    (95901) (powMod (2^166649) 21 ((2^166649+1)/3) 95900 1) 700 = true by decide +kernel)

private theorem r179174_96601 : RangeCond 179174 179198 96601 97301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 165249
    (96601) (powMod (2^165249) 21 ((2^165249+1)/3) 96600 1) 700 = true by decide +kernel)

private theorem r179174_97301 : RangeCond 179174 179198 97301 98001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 163849
    (97301) (powMod (2^163849) 21 ((2^163849+1)/3) 97300 1) 700 = true by decide +kernel)

private theorem r179174_98001 : RangeCond 179174 179198 98001 98701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 162449
    (98001) (powMod (2^162449) 21 ((2^162449+1)/3) 98000 1) 700 = true by decide +kernel)

private theorem r179174_98701 : RangeCond 179174 179198 98701 99401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 161049
    (98701) (powMod (2^161049) 21 ((2^161049+1)/3) 98700 1) 700 = true by decide +kernel)

private theorem r179174_99401 : RangeCond 179174 179198 99401 100101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 159649
    (99401) (powMod (2^159649) 21 ((2^159649+1)/3) 99400 1) 700 = true by decide +kernel)

private theorem r179174_100101 : RangeCond 179174 179198 100101 100801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 158249
    (100101) (powMod (2^158249) 21 ((2^158249+1)/3) 100100 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 100800"

private theorem r179174_100801 : RangeCond 179174 179198 100801 101501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 156849
    (100801) (powMod (2^156849) 21 ((2^156849+1)/3) 100800 1) 700 = true by decide +kernel)

private theorem r179174_101501 : RangeCond 179174 179198 101501 102201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 155449
    (101501) (powMod (2^155449) 21 ((2^155449+1)/3) 101500 1) 700 = true by decide +kernel)

private theorem r179174_102201 : RangeCond 179174 179198 102201 102901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 154049
    (102201) (powMod (2^154049) 21 ((2^154049+1)/3) 102200 1) 700 = true by decide +kernel)

private theorem r179174_102901 : RangeCond 179174 179198 102901 103601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 152649
    (102901) (powMod (2^152649) 21 ((2^152649+1)/3) 102900 1) 700 = true by decide +kernel)

private theorem r179174_103601 : RangeCond 179174 179198 103601 104301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 151249
    (103601) (powMod (2^151249) 21 ((2^151249+1)/3) 103600 1) 700 = true by decide +kernel)

private theorem r179174_104301 : RangeCond 179174 179198 104301 105001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 149849
    (104301) (powMod (2^149849) 21 ((2^149849+1)/3) 104300 1) 700 = true by decide +kernel)

private theorem r179174_105001 : RangeCond 179174 179198 105001 105701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 148449
    (105001) (powMod (2^148449) 21 ((2^148449+1)/3) 105000 1) 700 = true by decide +kernel)

private theorem r179174_105701 : RangeCond 179174 179198 105701 106401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 147049
    (105701) (powMod (2^147049) 21 ((2^147049+1)/3) 105700 1) 700 = true by decide +kernel)

private theorem r179174_106401 : RangeCond 179174 179198 106401 107101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 145649
    (106401) (powMod (2^145649) 21 ((2^145649+1)/3) 106400 1) 700 = true by decide +kernel)

private theorem r179174_107101 : RangeCond 179174 179198 107101 107801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 144249
    (107101) (powMod (2^144249) 21 ((2^144249+1)/3) 107100 1) 700 = true by decide +kernel)

private theorem r179174_107801 : RangeCond 179174 179198 107801 108501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 142849
    (107801) (powMod (2^142849) 21 ((2^142849+1)/3) 107800 1) 700 = true by decide +kernel)

private theorem r179174_108501 : RangeCond 179174 179198 108501 109201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 141449
    (108501) (powMod (2^141449) 21 ((2^141449+1)/3) 108500 1) 700 = true by decide +kernel)

private theorem r179174_109201 : RangeCond 179174 179198 109201 109901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 140049
    (109201) (powMod (2^140049) 21 ((2^140049+1)/3) 109200 1) 700 = true by decide +kernel)

private theorem r179174_109901 : RangeCond 179174 179198 109901 110601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 138649
    (109901) (powMod (2^138649) 21 ((2^138649+1)/3) 109900 1) 700 = true by decide +kernel)

private theorem r179174_110601 : RangeCond 179174 179198 110601 111301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 137249
    (110601) (powMod (2^137249) 21 ((2^137249+1)/3) 110600 1) 700 = true by decide +kernel)

private theorem r179174_111301 : RangeCond 179174 179198 111301 112001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 135849
    (111301) (powMod (2^135849) 21 ((2^135849+1)/3) 111300 1) 700 = true by decide +kernel)

private theorem r179174_112001 : RangeCond 179174 179198 112001 112701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 134449
    (112001) (powMod (2^134449) 21 ((2^134449+1)/3) 112000 1) 700 = true by decide +kernel)

private theorem r179174_112701 : RangeCond 179174 179198 112701 113401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 133049
    (112701) (powMod (2^133049) 21 ((2^133049+1)/3) 112700 1) 700 = true by decide +kernel)

private theorem r179174_113401 : RangeCond 179174 179198 113401 114101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 131649
    (113401) (powMod (2^131649) 21 ((2^131649+1)/3) 113400 1) 700 = true by decide +kernel)

private theorem r179174_114101 : RangeCond 179174 179198 114101 114801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 130249
    (114101) (powMod (2^130249) 21 ((2^130249+1)/3) 114100 1) 700 = true by decide +kernel)

private theorem r179174_114801 : RangeCond 179174 179198 114801 115501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 128849
    (114801) (powMod (2^128849) 21 ((2^128849+1)/3) 114800 1) 700 = true by decide +kernel)

private theorem r179174_115501 : RangeCond 179174 179198 115501 116201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 127449
    (115501) (powMod (2^127449) 21 ((2^127449+1)/3) 115500 1) 700 = true by decide +kernel)

private theorem r179174_116201 : RangeCond 179174 179198 116201 116901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 126049
    (116201) (powMod (2^126049) 21 ((2^126049+1)/3) 116200 1) 700 = true by decide +kernel)

private theorem r179174_116901 : RangeCond 179174 179198 116901 117601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 124649
    (116901) (powMod (2^124649) 21 ((2^124649+1)/3) 116900 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 117600"

private theorem r179174_117601 : RangeCond 179174 179198 117601 118301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 123249
    (117601) (powMod (2^123249) 21 ((2^123249+1)/3) 117600 1) 700 = true by decide +kernel)

private theorem r179174_118301 : RangeCond 179174 179198 118301 119001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 121849
    (118301) (powMod (2^121849) 21 ((2^121849+1)/3) 118300 1) 700 = true by decide +kernel)

private theorem r179174_119001 : RangeCond 179174 179198 119001 119701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 120449
    (119001) (powMod (2^120449) 21 ((2^120449+1)/3) 119000 1) 700 = true by decide +kernel)

private theorem r179174_119701 : RangeCond 179174 179198 119701 120401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 119049
    (119701) (powMod (2^119049) 21 ((2^119049+1)/3) 119700 1) 700 = true by decide +kernel)

private theorem r179174_120401 : RangeCond 179174 179198 120401 121101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 117649
    (120401) (powMod (2^117649) 21 ((2^117649+1)/3) 120400 1) 700 = true by decide +kernel)

private theorem r179174_121101 : RangeCond 179174 179198 121101 121801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 116249
    (121101) (powMod (2^116249) 21 ((2^116249+1)/3) 121100 1) 700 = true by decide +kernel)

private theorem r179174_121801 : RangeCond 179174 179198 121801 122501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 114849
    (121801) (powMod (2^114849) 21 ((2^114849+1)/3) 121800 1) 700 = true by decide +kernel)

private theorem r179174_122501 : RangeCond 179174 179198 122501 123201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 113449
    (122501) (powMod (2^113449) 21 ((2^113449+1)/3) 122500 1) 700 = true by decide +kernel)

private theorem r179174_123201 : RangeCond 179174 179198 123201 123901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 112049
    (123201) (powMod (2^112049) 21 ((2^112049+1)/3) 123200 1) 700 = true by decide +kernel)

private theorem r179174_123901 : RangeCond 179174 179198 123901 124601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 110649
    (123901) (powMod (2^110649) 21 ((2^110649+1)/3) 123900 1) 700 = true by decide +kernel)

private theorem r179174_124601 : RangeCond 179174 179198 124601 125301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 109249
    (124601) (powMod (2^109249) 21 ((2^109249+1)/3) 124600 1) 700 = true by decide +kernel)

private theorem r179174_125301 : RangeCond 179174 179198 125301 126001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 107849
    (125301) (powMod (2^107849) 21 ((2^107849+1)/3) 125300 1) 700 = true by decide +kernel)

private theorem r179174_126001 : RangeCond 179174 179198 126001 126701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 106449
    (126001) (powMod (2^106449) 21 ((2^106449+1)/3) 126000 1) 700 = true by decide +kernel)

private theorem r179174_126701 : RangeCond 179174 179198 126701 127401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 105049
    (126701) (powMod (2^105049) 21 ((2^105049+1)/3) 126700 1) 700 = true by decide +kernel)

private theorem r179174_127401 : RangeCond 179174 179198 127401 128101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 103649
    (127401) (powMod (2^103649) 21 ((2^103649+1)/3) 127400 1) 700 = true by decide +kernel)

private theorem r179174_128101 : RangeCond 179174 179198 128101 128801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 102249
    (128101) (powMod (2^102249) 21 ((2^102249+1)/3) 128100 1) 700 = true by decide +kernel)

private theorem r179174_128801 : RangeCond 179174 179198 128801 129501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 100849
    (128801) (powMod (2^100849) 21 ((2^100849+1)/3) 128800 1) 700 = true by decide +kernel)

private theorem r179174_129501 : RangeCond 179174 179198 129501 130201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 99449
    (129501) (powMod (2^99449) 21 ((2^99449+1)/3) 129500 1) 700 = true by decide +kernel)

private theorem r179174_130201 : RangeCond 179174 179198 130201 130901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 98049
    (130201) (powMod (2^98049) 21 ((2^98049+1)/3) 130200 1) 700 = true by decide +kernel)

private theorem r179174_130901 : RangeCond 179174 179198 130901 131601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 96649
    (130901) (powMod (2^96649) 21 ((2^96649+1)/3) 130900 1) 700 = true by decide +kernel)

private theorem r179174_131601 : RangeCond 179174 179198 131601 132301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 95249
    (131601) (powMod (2^95249) 21 ((2^95249+1)/3) 131600 1) 700 = true by decide +kernel)

private theorem r179174_132301 : RangeCond 179174 179198 132301 133001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 93849
    (132301) (powMod (2^93849) 21 ((2^93849+1)/3) 132300 1) 700 = true by decide +kernel)

private theorem r179174_133001 : RangeCond 179174 179198 133001 133701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 92449
    (133001) (powMod (2^92449) 21 ((2^92449+1)/3) 133000 1) 700 = true by decide +kernel)

private theorem r179174_133701 : RangeCond 179174 179198 133701 134401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 91049
    (133701) (powMod (2^91049) 21 ((2^91049+1)/3) 133700 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 134400"

private theorem r179174_134401 : RangeCond 179174 179198 134401 135101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 89649
    (134401) (powMod (2^89649) 21 ((2^89649+1)/3) 134400 1) 700 = true by decide +kernel)

private theorem r179174_135101 : RangeCond 179174 179198 135101 135801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 88249
    (135101) (powMod (2^88249) 21 ((2^88249+1)/3) 135100 1) 700 = true by decide +kernel)

private theorem r179174_135801 : RangeCond 179174 179198 135801 136501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 86849
    (135801) (powMod (2^86849) 21 ((2^86849+1)/3) 135800 1) 700 = true by decide +kernel)

private theorem r179174_136501 : RangeCond 179174 179198 136501 137201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 85449
    (136501) (powMod (2^85449) 21 ((2^85449+1)/3) 136500 1) 700 = true by decide +kernel)

private theorem r179174_137201 : RangeCond 179174 179198 137201 137901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 84049
    (137201) (powMod (2^84049) 21 ((2^84049+1)/3) 137200 1) 700 = true by decide +kernel)

private theorem r179174_137901 : RangeCond 179174 179198 137901 138601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 82649
    (137901) (powMod (2^82649) 21 ((2^82649+1)/3) 137900 1) 700 = true by decide +kernel)

private theorem r179174_138601 : RangeCond 179174 179198 138601 139301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 81249
    (138601) (powMod (2^81249) 21 ((2^81249+1)/3) 138600 1) 700 = true by decide +kernel)

private theorem r179174_139301 : RangeCond 179174 179198 139301 140001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 79849
    (139301) (powMod (2^79849) 21 ((2^79849+1)/3) 139300 1) 700 = true by decide +kernel)

private theorem r179174_140001 : RangeCond 179174 179198 140001 140701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 78449
    (140001) (powMod (2^78449) 21 ((2^78449+1)/3) 140000 1) 700 = true by decide +kernel)

private theorem r179174_140701 : RangeCond 179174 179198 140701 141401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 77049
    (140701) (powMod (2^77049) 21 ((2^77049+1)/3) 140700 1) 700 = true by decide +kernel)

private theorem r179174_141401 : RangeCond 179174 179198 141401 142101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 75649
    (141401) (powMod (2^75649) 21 ((2^75649+1)/3) 141400 1) 700 = true by decide +kernel)

private theorem r179174_142101 : RangeCond 179174 179198 142101 142801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 74249
    (142101) (powMod (2^74249) 21 ((2^74249+1)/3) 142100 1) 700 = true by decide +kernel)

private theorem r179174_142801 : RangeCond 179174 179198 142801 143501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 72849
    (142801) (powMod (2^72849) 21 ((2^72849+1)/3) 142800 1) 700 = true by decide +kernel)

private theorem r179174_143501 : RangeCond 179174 179198 143501 144201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 71449
    (143501) (powMod (2^71449) 21 ((2^71449+1)/3) 143500 1) 700 = true by decide +kernel)

private theorem r179174_144201 : RangeCond 179174 179198 144201 144901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 70049
    (144201) (powMod (2^70049) 21 ((2^70049+1)/3) 144200 1) 700 = true by decide +kernel)

private theorem r179174_144901 : RangeCond 179174 179198 144901 145601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 68649
    (144901) (powMod (2^68649) 21 ((2^68649+1)/3) 144900 1) 700 = true by decide +kernel)

private theorem r179174_145601 : RangeCond 179174 179198 145601 146301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 67249
    (145601) (powMod (2^67249) 21 ((2^67249+1)/3) 145600 1) 700 = true by decide +kernel)

private theorem r179174_146301 : RangeCond 179174 179198 146301 147001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 65849
    (146301) (powMod (2^65849) 21 ((2^65849+1)/3) 146300 1) 700 = true by decide +kernel)

private theorem r179174_147001 : RangeCond 179174 179198 147001 147701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 64449
    (147001) (powMod (2^64449) 21 ((2^64449+1)/3) 147000 1) 700 = true by decide +kernel)

private theorem r179174_147701 : RangeCond 179174 179198 147701 148401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 63049
    (147701) (powMod (2^63049) 21 ((2^63049+1)/3) 147700 1) 700 = true by decide +kernel)

private theorem r179174_148401 : RangeCond 179174 179198 148401 149101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 61649
    (148401) (powMod (2^61649) 21 ((2^61649+1)/3) 148400 1) 700 = true by decide +kernel)

private theorem r179174_149101 : RangeCond 179174 179198 149101 149801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 60249
    (149101) (powMod (2^60249) 21 ((2^60249+1)/3) 149100 1) 700 = true by decide +kernel)

private theorem r179174_149801 : RangeCond 179174 179198 149801 150501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 58849
    (149801) (powMod (2^58849) 21 ((2^58849+1)/3) 149800 1) 700 = true by decide +kernel)

private theorem r179174_150501 : RangeCond 179174 179198 150501 151201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 57449
    (150501) (powMod (2^57449) 21 ((2^57449+1)/3) 150500 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 151200"

private theorem r179174_151201 : RangeCond 179174 179198 151201 151901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 56049
    (151201) (powMod (2^56049) 21 ((2^56049+1)/3) 151200 1) 700 = true by decide +kernel)

private theorem r179174_151901 : RangeCond 179174 179198 151901 152601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 54649
    (151901) (powMod (2^54649) 21 ((2^54649+1)/3) 151900 1) 700 = true by decide +kernel)

private theorem r179174_152601 : RangeCond 179174 179198 152601 153301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 53249
    (152601) (powMod (2^53249) 21 ((2^53249+1)/3) 152600 1) 700 = true by decide +kernel)

private theorem r179174_153301 : RangeCond 179174 179198 153301 154001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 51849
    (153301) (powMod (2^51849) 21 ((2^51849+1)/3) 153300 1) 700 = true by decide +kernel)

private theorem r179174_154001 : RangeCond 179174 179198 154001 154701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 50449
    (154001) (powMod (2^50449) 21 ((2^50449+1)/3) 154000 1) 700 = true by decide +kernel)

private theorem r179174_154701 : RangeCond 179174 179198 154701 155401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 49049
    (154701) (powMod (2^49049) 21 ((2^49049+1)/3) 154700 1) 700 = true by decide +kernel)

private theorem r179174_155401 : RangeCond 179174 179198 155401 156101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 47649
    (155401) (powMod (2^47649) 21 ((2^47649+1)/3) 155400 1) 700 = true by decide +kernel)

private theorem r179174_156101 : RangeCond 179174 179198 156101 156801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 46249
    (156101) (powMod (2^46249) 21 ((2^46249+1)/3) 156100 1) 700 = true by decide +kernel)

private theorem r179174_156801 : RangeCond 179174 179198 156801 157501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 44849
    (156801) (powMod (2^44849) 21 ((2^44849+1)/3) 156800 1) 700 = true by decide +kernel)

private theorem r179174_157501 : RangeCond 179174 179198 157501 158201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 43449
    (157501) (powMod (2^43449) 21 ((2^43449+1)/3) 157500 1) 700 = true by decide +kernel)

private theorem r179174_158201 : RangeCond 179174 179198 158201 158901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 42049
    (158201) (powMod (2^42049) 21 ((2^42049+1)/3) 158200 1) 700 = true by decide +kernel)

private theorem r179174_158901 : RangeCond 179174 179198 158901 159601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 40649
    (158901) (powMod (2^40649) 21 ((2^40649+1)/3) 158900 1) 700 = true by decide +kernel)

private theorem r179174_159601 : RangeCond 179174 179198 159601 160301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 39249
    (159601) (powMod (2^39249) 21 ((2^39249+1)/3) 159600 1) 700 = true by decide +kernel)

private theorem r179174_160301 : RangeCond 179174 179198 160301 161001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 37849
    (160301) (powMod (2^37849) 21 ((2^37849+1)/3) 160300 1) 700 = true by decide +kernel)

private theorem r179174_161001 : RangeCond 179174 179198 161001 161701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 36449
    (161001) (powMod (2^36449) 21 ((2^36449+1)/3) 161000 1) 700 = true by decide +kernel)

private theorem r179174_161701 : RangeCond 179174 179198 161701 162401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 35049
    (161701) (powMod (2^35049) 21 ((2^35049+1)/3) 161700 1) 700 = true by decide +kernel)

private theorem r179174_162401 : RangeCond 179174 179198 162401 163101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 33649
    (162401) (powMod (2^33649) 21 ((2^33649+1)/3) 162400 1) 700 = true by decide +kernel)

private theorem r179174_163101 : RangeCond 179174 179198 163101 163801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 32249
    (163101) (powMod (2^32249) 21 ((2^32249+1)/3) 163100 1) 700 = true by decide +kernel)

private theorem r179174_163801 : RangeCond 179174 179198 163801 164501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 30849
    (163801) (powMod (2^30849) 21 ((2^30849+1)/3) 163800 1) 700 = true by decide +kernel)

private theorem r179174_164501 : RangeCond 179174 179198 164501 165201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 29449
    (164501) (powMod (2^29449) 21 ((2^29449+1)/3) 164500 1) 700 = true by decide +kernel)

private theorem r179174_165201 : RangeCond 179174 179198 165201 165901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 28049
    (165201) (powMod (2^28049) 21 ((2^28049+1)/3) 165200 1) 700 = true by decide +kernel)

private theorem r179174_165901 : RangeCond 179174 179198 165901 166601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 26649
    (165901) (powMod (2^26649) 21 ((2^26649+1)/3) 165900 1) 700 = true by decide +kernel)

private theorem r179174_166601 : RangeCond 179174 179198 166601 167301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 25249
    (166601) (powMod (2^25249) 21 ((2^25249+1)/3) 166600 1) 700 = true by decide +kernel)

private theorem r179174_167301 : RangeCond 179174 179198 167301 168001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 23849
    (167301) (powMod (2^23849) 21 ((2^23849+1)/3) 167300 1) 700 = true by decide +kernel)

#eval IO.println "N = 179174, checked through 168000"

private theorem r179174_168001 : RangeCond 179174 179198 168001 168701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 22449
    (168001) (powMod (2^22449) 21 ((2^22449+1)/3) 168000 1) 700 = true by decide +kernel)

private theorem r179174_168701 : RangeCond 179174 179198 168701 169401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 21049
    (168701) (powMod (2^21049) 21 ((2^21049+1)/3) 168700 1) 700 = true by decide +kernel)

private theorem r179174_169401 : RangeCond 179174 179198 169401 170101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 19649
    (169401) (powMod (2^19649) 21 ((2^19649+1)/3) 169400 1) 700 = true by decide +kernel)

private theorem r179174_170101 : RangeCond 179174 179198 170101 170801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 18249
    (170101) (powMod (2^18249) 21 ((2^18249+1)/3) 170100 1) 700 = true by decide +kernel)

private theorem r179174_170801 : RangeCond 179174 179198 170801 171501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 16849
    (170801) (powMod (2^16849) 21 ((2^16849+1)/3) 170800 1) 700 = true by decide +kernel)

private theorem r179174_171501 : RangeCond 179174 179198 171501 172201 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 15449
    (171501) (powMod (2^15449) 21 ((2^15449+1)/3) 171500 1) 700 = true by decide +kernel)

private theorem r179174_172201 : RangeCond 179174 179198 172201 172901 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 14049
    (172201) (powMod (2^14049) 21 ((2^14049+1)/3) 172200 1) 700 = true by decide +kernel)

private theorem r179174_172901 : RangeCond 179174 179198 172901 173601 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 12649
    (172901) (powMod (2^12649) 21 ((2^12649+1)/3) 172900 1) 700 = true by decide +kernel)

private theorem r179174_173601 : RangeCond 179174 179198 173601 174301 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 11249
    (173601) (powMod (2^11249) 21 ((2^11249+1)/3) 173600 1) 700 = true by decide +kernel)

private theorem r179174_174301 : RangeCond 179174 179198 174301 175001 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 9849
    (174301) (powMod (2^9849) 21 ((2^9849+1)/3) 174300 1) 700 = true by decide +kernel)

private theorem r179174_175001 : RangeCond 179174 179198 175001 175701 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 8449
    (175001) (powMod (2^8449) 21 ((2^8449+1)/3) 175000 1) 700 = true by decide +kernel)

private theorem r179174_175701 : RangeCond 179174 179198 175701 176401 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 7049
    (175701) (powMod (2^7049) 21 ((2^7049+1)/3) 175700 1) 700 = true by decide +kernel)

private theorem r179174_176401 : RangeCond 179174 179198 176401 177101 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 5649
    (176401) (powMod (2^5649) 21 ((2^5649+1)/3) 176400 1) 700 = true by decide +kernel)

private theorem r179174_177101 : RangeCond 179174 179198 177101 177801 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 4249
    (177101) (powMod (2^4249) 21 ((2^4249+1)/3) 177100 1) 700 = true by decide +kernel)

private theorem r179174_177801 : RangeCond 179174 179198 177801 178501 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 2849
    (177801) (powMod (2^2849) 21 ((2^2849+1)/3) 177800 1) 700 = true by decide +kernel)

private theorem r179174_178501 : RangeCond 179174 179198 178501 179175 := by
  exact reducedRange_sound (show reducedRange 179174 179198 24 1449
    (178501) (powMod (2^1449) 21 ((2^1449+1)/3) 178500 1) 674 = true by decide +kernel)

theorem pairs179174 : AllPairs 179174 179198 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_1 r179174_701) (RangeCond.trans r179174_1401 r179174_2101)) (RangeCond.trans (RangeCond.trans r179174_2801 r179174_3501) (RangeCond.trans r179174_4201 r179174_4901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_5601 r179174_6301) (RangeCond.trans r179174_7001 r179174_7701)) (RangeCond.trans (RangeCond.trans r179174_8401 r179174_9101) (RangeCond.trans r179174_9801 r179174_10501)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_11201 r179174_11901) (RangeCond.trans r179174_12601 r179174_13301)) (RangeCond.trans (RangeCond.trans r179174_14001 r179174_14701) (RangeCond.trans r179174_15401 r179174_16101))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_16801 r179174_17501) (RangeCond.trans r179174_18201 r179174_18901)) (RangeCond.trans (RangeCond.trans r179174_19601 r179174_20301) (RangeCond.trans r179174_21001 r179174_21701))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_22401 r179174_23101) (RangeCond.trans r179174_23801 r179174_24501)) (RangeCond.trans (RangeCond.trans r179174_25201 r179174_25901) (RangeCond.trans r179174_26601 r179174_27301))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_28001 r179174_28701) (RangeCond.trans r179174_29401 r179174_30101)) (RangeCond.trans (RangeCond.trans r179174_30801 r179174_31501) (RangeCond.trans r179174_32201 r179174_32901)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_33601 r179174_34301) (RangeCond.trans r179174_35001 r179174_35701)) (RangeCond.trans (RangeCond.trans r179174_36401 r179174_37101) (RangeCond.trans r179174_37801 r179174_38501))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_39201 r179174_39901) (RangeCond.trans r179174_40601 r179174_41301)) (RangeCond.trans (RangeCond.trans r179174_42001 r179174_42701) (RangeCond.trans r179174_43401 r179174_44101)))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_44801 r179174_45501) (RangeCond.trans r179174_46201 r179174_46901)) (RangeCond.trans (RangeCond.trans r179174_47601 r179174_48301) (RangeCond.trans r179174_49001 r179174_49701))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_50401 r179174_51101) (RangeCond.trans r179174_51801 r179174_52501)) (RangeCond.trans (RangeCond.trans r179174_53201 r179174_53901) (RangeCond.trans r179174_54601 r179174_55301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_56001 r179174_56701) (RangeCond.trans r179174_57401 r179174_58101)) (RangeCond.trans (RangeCond.trans r179174_58801 r179174_59501) (RangeCond.trans r179174_60201 r179174_60901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_61601 r179174_62301) (RangeCond.trans r179174_63001 r179174_63701)) (RangeCond.trans (RangeCond.trans r179174_64401 r179174_65101) (RangeCond.trans r179174_65801 r179174_66501))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_67201 r179174_67901) (RangeCond.trans r179174_68601 r179174_69301)) (RangeCond.trans (RangeCond.trans r179174_70001 r179174_70701) (RangeCond.trans r179174_71401 r179174_72101))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_72801 r179174_73501) (RangeCond.trans r179174_74201 r179174_74901)) (RangeCond.trans (RangeCond.trans r179174_75601 r179174_76301) (RangeCond.trans r179174_77001 r179174_77701)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_78401 r179174_79101) (RangeCond.trans r179174_79801 r179174_80501)) (RangeCond.trans (RangeCond.trans r179174_81201 r179174_81901) (RangeCond.trans r179174_82601 r179174_83301))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_84001 r179174_84701) (RangeCond.trans r179174_85401 r179174_86101)) (RangeCond.trans (RangeCond.trans r179174_86801 r179174_87501) (RangeCond.trans r179174_88201 r179174_88901))))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_89601 r179174_90301) (RangeCond.trans r179174_91001 r179174_91701)) (RangeCond.trans (RangeCond.trans r179174_92401 r179174_93101) (RangeCond.trans r179174_93801 r179174_94501))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_95201 r179174_95901) (RangeCond.trans r179174_96601 r179174_97301)) (RangeCond.trans (RangeCond.trans r179174_98001 r179174_98701) (RangeCond.trans r179174_99401 r179174_100101)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_100801 r179174_101501) (RangeCond.trans r179174_102201 r179174_102901)) (RangeCond.trans (RangeCond.trans r179174_103601 r179174_104301) (RangeCond.trans r179174_105001 r179174_105701))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_106401 r179174_107101) (RangeCond.trans r179174_107801 r179174_108501)) (RangeCond.trans (RangeCond.trans r179174_109201 r179174_109901) (RangeCond.trans r179174_110601 r179174_111301))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_112001 r179174_112701) (RangeCond.trans r179174_113401 r179174_114101)) (RangeCond.trans (RangeCond.trans r179174_114801 r179174_115501) (RangeCond.trans r179174_116201 r179174_116901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_117601 r179174_118301) (RangeCond.trans r179174_119001 r179174_119701)) (RangeCond.trans (RangeCond.trans r179174_120401 r179174_121101) (RangeCond.trans r179174_121801 r179174_122501)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_123201 r179174_123901) (RangeCond.trans r179174_124601 r179174_125301)) (RangeCond.trans (RangeCond.trans r179174_126001 r179174_126701) (RangeCond.trans r179174_127401 r179174_128101))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_128801 r179174_129501) (RangeCond.trans r179174_130201 r179174_130901)) (RangeCond.trans (RangeCond.trans r179174_131601 r179174_132301) (RangeCond.trans r179174_133001 r179174_133701)))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_134401 r179174_135101) (RangeCond.trans r179174_135801 r179174_136501)) (RangeCond.trans (RangeCond.trans r179174_137201 r179174_137901) (RangeCond.trans r179174_138601 r179174_139301))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_140001 r179174_140701) (RangeCond.trans r179174_141401 r179174_142101)) (RangeCond.trans (RangeCond.trans r179174_142801 r179174_143501) (RangeCond.trans r179174_144201 r179174_144901)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_145601 r179174_146301) (RangeCond.trans r179174_147001 r179174_147701)) (RangeCond.trans (RangeCond.trans r179174_148401 r179174_149101) (RangeCond.trans r179174_149801 r179174_150501))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_151201 r179174_151901) (RangeCond.trans r179174_152601 r179174_153301)) (RangeCond.trans (RangeCond.trans r179174_154001 r179174_154701) (RangeCond.trans r179174_155401 r179174_156101))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_156801 r179174_157501) (RangeCond.trans r179174_158201 r179174_158901)) (RangeCond.trans (RangeCond.trans r179174_159601 r179174_160301) (RangeCond.trans r179174_161001 r179174_161701))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_162401 r179174_163101) (RangeCond.trans r179174_163801 r179174_164501)) (RangeCond.trans (RangeCond.trans r179174_165201 r179174_165901) (RangeCond.trans r179174_166601 r179174_167301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_168001 r179174_168701) (RangeCond.trans r179174_169401 r179174_170101)) (RangeCond.trans (RangeCond.trans r179174_170801 r179174_171501) (RangeCond.trans r179174_172201 r179174_172901))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r179174_173601 r179174_174301) (RangeCond.trans r179174_175001 r179174_175701)) (RangeCond.trans (RangeCond.trans r179174_176401 r179174_177101) (RangeCond.trans r179174_177801 r179174_178501))))))))

#print axioms pairs179174

end Cycle108
