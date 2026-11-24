import ReducedHeight

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem r113037_1 : RangeCond 113037 113061 1 701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 226175
    (1) (powMod (2^226175) 21 ((2^226175+1)/3) 0 1) 700 = true by decide +kernel)

private theorem r113037_701 : RangeCond 113037 113061 701 1401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 224775
    (701) (powMod (2^224775) 21 ((2^224775+1)/3) 700 1) 700 = true by decide +kernel)

private theorem r113037_1401 : RangeCond 113037 113061 1401 2101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 223375
    (1401) (powMod (2^223375) 21 ((2^223375+1)/3) 1400 1) 700 = true by decide +kernel)

private theorem r113037_2101 : RangeCond 113037 113061 2101 2801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 221975
    (2101) (powMod (2^221975) 21 ((2^221975+1)/3) 2100 1) 700 = true by decide +kernel)

private theorem r113037_2801 : RangeCond 113037 113061 2801 3501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 220575
    (2801) (powMod (2^220575) 21 ((2^220575+1)/3) 2800 1) 700 = true by decide +kernel)

private theorem r113037_3501 : RangeCond 113037 113061 3501 4201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 219175
    (3501) (powMod (2^219175) 21 ((2^219175+1)/3) 3500 1) 700 = true by decide +kernel)

private theorem r113037_4201 : RangeCond 113037 113061 4201 4901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 217775
    (4201) (powMod (2^217775) 21 ((2^217775+1)/3) 4200 1) 700 = true by decide +kernel)

private theorem r113037_4901 : RangeCond 113037 113061 4901 5601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 216375
    (4901) (powMod (2^216375) 21 ((2^216375+1)/3) 4900 1) 700 = true by decide +kernel)

private theorem r113037_5601 : RangeCond 113037 113061 5601 6301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 214975
    (5601) (powMod (2^214975) 21 ((2^214975+1)/3) 5600 1) 700 = true by decide +kernel)

private theorem r113037_6301 : RangeCond 113037 113061 6301 7001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 213575
    (6301) (powMod (2^213575) 21 ((2^213575+1)/3) 6300 1) 700 = true by decide +kernel)

private theorem r113037_7001 : RangeCond 113037 113061 7001 7701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 212175
    (7001) (powMod (2^212175) 21 ((2^212175+1)/3) 7000 1) 700 = true by decide +kernel)

private theorem r113037_7701 : RangeCond 113037 113061 7701 8401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 210775
    (7701) (powMod (2^210775) 21 ((2^210775+1)/3) 7700 1) 700 = true by decide +kernel)

private theorem r113037_8401 : RangeCond 113037 113061 8401 9101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 209375
    (8401) (powMod (2^209375) 21 ((2^209375+1)/3) 8400 1) 700 = true by decide +kernel)

private theorem r113037_9101 : RangeCond 113037 113061 9101 9801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 207975
    (9101) (powMod (2^207975) 21 ((2^207975+1)/3) 9100 1) 700 = true by decide +kernel)

private theorem r113037_9801 : RangeCond 113037 113061 9801 10501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 206575
    (9801) (powMod (2^206575) 21 ((2^206575+1)/3) 9800 1) 700 = true by decide +kernel)

private theorem r113037_10501 : RangeCond 113037 113061 10501 11201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 205175
    (10501) (powMod (2^205175) 21 ((2^205175+1)/3) 10500 1) 700 = true by decide +kernel)

private theorem r113037_11201 : RangeCond 113037 113061 11201 11901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 203775
    (11201) (powMod (2^203775) 21 ((2^203775+1)/3) 11200 1) 700 = true by decide +kernel)

private theorem r113037_11901 : RangeCond 113037 113061 11901 12601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 202375
    (11901) (powMod (2^202375) 21 ((2^202375+1)/3) 11900 1) 700 = true by decide +kernel)

private theorem r113037_12601 : RangeCond 113037 113061 12601 13301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 200975
    (12601) (powMod (2^200975) 21 ((2^200975+1)/3) 12600 1) 700 = true by decide +kernel)

private theorem r113037_13301 : RangeCond 113037 113061 13301 14001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 199575
    (13301) (powMod (2^199575) 21 ((2^199575+1)/3) 13300 1) 700 = true by decide +kernel)

private theorem r113037_14001 : RangeCond 113037 113061 14001 14701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 198175
    (14001) (powMod (2^198175) 21 ((2^198175+1)/3) 14000 1) 700 = true by decide +kernel)

private theorem r113037_14701 : RangeCond 113037 113061 14701 15401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 196775
    (14701) (powMod (2^196775) 21 ((2^196775+1)/3) 14700 1) 700 = true by decide +kernel)

private theorem r113037_15401 : RangeCond 113037 113061 15401 16101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 195375
    (15401) (powMod (2^195375) 21 ((2^195375+1)/3) 15400 1) 700 = true by decide +kernel)

private theorem r113037_16101 : RangeCond 113037 113061 16101 16801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 193975
    (16101) (powMod (2^193975) 21 ((2^193975+1)/3) 16100 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 16800"

private theorem r113037_16801 : RangeCond 113037 113061 16801 17501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 192575
    (16801) (powMod (2^192575) 21 ((2^192575+1)/3) 16800 1) 700 = true by decide +kernel)

private theorem r113037_17501 : RangeCond 113037 113061 17501 18201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 191175
    (17501) (powMod (2^191175) 21 ((2^191175+1)/3) 17500 1) 700 = true by decide +kernel)

private theorem r113037_18201 : RangeCond 113037 113061 18201 18901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 189775
    (18201) (powMod (2^189775) 21 ((2^189775+1)/3) 18200 1) 700 = true by decide +kernel)

private theorem r113037_18901 : RangeCond 113037 113061 18901 19601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 188375
    (18901) (powMod (2^188375) 21 ((2^188375+1)/3) 18900 1) 700 = true by decide +kernel)

private theorem r113037_19601 : RangeCond 113037 113061 19601 20301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 186975
    (19601) (powMod (2^186975) 21 ((2^186975+1)/3) 19600 1) 700 = true by decide +kernel)

private theorem r113037_20301 : RangeCond 113037 113061 20301 21001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 185575
    (20301) (powMod (2^185575) 21 ((2^185575+1)/3) 20300 1) 700 = true by decide +kernel)

private theorem r113037_21001 : RangeCond 113037 113061 21001 21701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 184175
    (21001) (powMod (2^184175) 21 ((2^184175+1)/3) 21000 1) 700 = true by decide +kernel)

private theorem r113037_21701 : RangeCond 113037 113061 21701 22401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 182775
    (21701) (powMod (2^182775) 21 ((2^182775+1)/3) 21700 1) 700 = true by decide +kernel)

private theorem r113037_22401 : RangeCond 113037 113061 22401 23101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 181375
    (22401) (powMod (2^181375) 21 ((2^181375+1)/3) 22400 1) 700 = true by decide +kernel)

private theorem r113037_23101 : RangeCond 113037 113061 23101 23801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 179975
    (23101) (powMod (2^179975) 21 ((2^179975+1)/3) 23100 1) 700 = true by decide +kernel)

private theorem r113037_23801 : RangeCond 113037 113061 23801 24501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 178575
    (23801) (powMod (2^178575) 21 ((2^178575+1)/3) 23800 1) 700 = true by decide +kernel)

private theorem r113037_24501 : RangeCond 113037 113061 24501 25201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 177175
    (24501) (powMod (2^177175) 21 ((2^177175+1)/3) 24500 1) 700 = true by decide +kernel)

private theorem r113037_25201 : RangeCond 113037 113061 25201 25901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 175775
    (25201) (powMod (2^175775) 21 ((2^175775+1)/3) 25200 1) 700 = true by decide +kernel)

private theorem r113037_25901 : RangeCond 113037 113061 25901 26601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 174375
    (25901) (powMod (2^174375) 21 ((2^174375+1)/3) 25900 1) 700 = true by decide +kernel)

private theorem r113037_26601 : RangeCond 113037 113061 26601 27301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 172975
    (26601) (powMod (2^172975) 21 ((2^172975+1)/3) 26600 1) 700 = true by decide +kernel)

private theorem r113037_27301 : RangeCond 113037 113061 27301 28001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 171575
    (27301) (powMod (2^171575) 21 ((2^171575+1)/3) 27300 1) 700 = true by decide +kernel)

private theorem r113037_28001 : RangeCond 113037 113061 28001 28701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 170175
    (28001) (powMod (2^170175) 21 ((2^170175+1)/3) 28000 1) 700 = true by decide +kernel)

private theorem r113037_28701 : RangeCond 113037 113061 28701 29401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 168775
    (28701) (powMod (2^168775) 21 ((2^168775+1)/3) 28700 1) 700 = true by decide +kernel)

private theorem r113037_29401 : RangeCond 113037 113061 29401 30101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 167375
    (29401) (powMod (2^167375) 21 ((2^167375+1)/3) 29400 1) 700 = true by decide +kernel)

private theorem r113037_30101 : RangeCond 113037 113061 30101 30801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 165975
    (30101) (powMod (2^165975) 21 ((2^165975+1)/3) 30100 1) 700 = true by decide +kernel)

private theorem r113037_30801 : RangeCond 113037 113061 30801 31501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 164575
    (30801) (powMod (2^164575) 21 ((2^164575+1)/3) 30800 1) 700 = true by decide +kernel)

private theorem r113037_31501 : RangeCond 113037 113061 31501 32201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 163175
    (31501) (powMod (2^163175) 21 ((2^163175+1)/3) 31500 1) 700 = true by decide +kernel)

private theorem r113037_32201 : RangeCond 113037 113061 32201 32901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 161775
    (32201) (powMod (2^161775) 21 ((2^161775+1)/3) 32200 1) 700 = true by decide +kernel)

private theorem r113037_32901 : RangeCond 113037 113061 32901 33601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 160375
    (32901) (powMod (2^160375) 21 ((2^160375+1)/3) 32900 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 33600"

private theorem r113037_33601 : RangeCond 113037 113061 33601 34301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 158975
    (33601) (powMod (2^158975) 21 ((2^158975+1)/3) 33600 1) 700 = true by decide +kernel)

private theorem r113037_34301 : RangeCond 113037 113061 34301 35001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 157575
    (34301) (powMod (2^157575) 21 ((2^157575+1)/3) 34300 1) 700 = true by decide +kernel)

private theorem r113037_35001 : RangeCond 113037 113061 35001 35701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 156175
    (35001) (powMod (2^156175) 21 ((2^156175+1)/3) 35000 1) 700 = true by decide +kernel)

private theorem r113037_35701 : RangeCond 113037 113061 35701 36401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 154775
    (35701) (powMod (2^154775) 21 ((2^154775+1)/3) 35700 1) 700 = true by decide +kernel)

private theorem r113037_36401 : RangeCond 113037 113061 36401 37101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 153375
    (36401) (powMod (2^153375) 21 ((2^153375+1)/3) 36400 1) 700 = true by decide +kernel)

private theorem r113037_37101 : RangeCond 113037 113061 37101 37801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 151975
    (37101) (powMod (2^151975) 21 ((2^151975+1)/3) 37100 1) 700 = true by decide +kernel)

private theorem r113037_37801 : RangeCond 113037 113061 37801 38501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 150575
    (37801) (powMod (2^150575) 21 ((2^150575+1)/3) 37800 1) 700 = true by decide +kernel)

private theorem r113037_38501 : RangeCond 113037 113061 38501 39201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 149175
    (38501) (powMod (2^149175) 21 ((2^149175+1)/3) 38500 1) 700 = true by decide +kernel)

private theorem r113037_39201 : RangeCond 113037 113061 39201 39901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 147775
    (39201) (powMod (2^147775) 21 ((2^147775+1)/3) 39200 1) 700 = true by decide +kernel)

private theorem r113037_39901 : RangeCond 113037 113061 39901 40601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 146375
    (39901) (powMod (2^146375) 21 ((2^146375+1)/3) 39900 1) 700 = true by decide +kernel)

private theorem r113037_40601 : RangeCond 113037 113061 40601 41301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 144975
    (40601) (powMod (2^144975) 21 ((2^144975+1)/3) 40600 1) 700 = true by decide +kernel)

private theorem r113037_41301 : RangeCond 113037 113061 41301 42001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 143575
    (41301) (powMod (2^143575) 21 ((2^143575+1)/3) 41300 1) 700 = true by decide +kernel)

private theorem r113037_42001 : RangeCond 113037 113061 42001 42701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 142175
    (42001) (powMod (2^142175) 21 ((2^142175+1)/3) 42000 1) 700 = true by decide +kernel)

private theorem r113037_42701 : RangeCond 113037 113061 42701 43401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 140775
    (42701) (powMod (2^140775) 21 ((2^140775+1)/3) 42700 1) 700 = true by decide +kernel)

private theorem r113037_43401 : RangeCond 113037 113061 43401 44101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 139375
    (43401) (powMod (2^139375) 21 ((2^139375+1)/3) 43400 1) 700 = true by decide +kernel)

private theorem r113037_44101 : RangeCond 113037 113061 44101 44801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 137975
    (44101) (powMod (2^137975) 21 ((2^137975+1)/3) 44100 1) 700 = true by decide +kernel)

private theorem r113037_44801 : RangeCond 113037 113061 44801 45501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 136575
    (44801) (powMod (2^136575) 21 ((2^136575+1)/3) 44800 1) 700 = true by decide +kernel)

private theorem r113037_45501 : RangeCond 113037 113061 45501 46201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 135175
    (45501) (powMod (2^135175) 21 ((2^135175+1)/3) 45500 1) 700 = true by decide +kernel)

private theorem r113037_46201 : RangeCond 113037 113061 46201 46901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 133775
    (46201) (powMod (2^133775) 21 ((2^133775+1)/3) 46200 1) 700 = true by decide +kernel)

private theorem r113037_46901 : RangeCond 113037 113061 46901 47601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 132375
    (46901) (powMod (2^132375) 21 ((2^132375+1)/3) 46900 1) 700 = true by decide +kernel)

private theorem r113037_47601 : RangeCond 113037 113061 47601 48301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 130975
    (47601) (powMod (2^130975) 21 ((2^130975+1)/3) 47600 1) 700 = true by decide +kernel)

private theorem r113037_48301 : RangeCond 113037 113061 48301 49001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 129575
    (48301) (powMod (2^129575) 21 ((2^129575+1)/3) 48300 1) 700 = true by decide +kernel)

private theorem r113037_49001 : RangeCond 113037 113061 49001 49701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 128175
    (49001) (powMod (2^128175) 21 ((2^128175+1)/3) 49000 1) 700 = true by decide +kernel)

private theorem r113037_49701 : RangeCond 113037 113061 49701 50401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 126775
    (49701) (powMod (2^126775) 21 ((2^126775+1)/3) 49700 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 50400"

private theorem r113037_50401 : RangeCond 113037 113061 50401 51101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 125375
    (50401) (powMod (2^125375) 21 ((2^125375+1)/3) 50400 1) 700 = true by decide +kernel)

private theorem r113037_51101 : RangeCond 113037 113061 51101 51801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 123975
    (51101) (powMod (2^123975) 21 ((2^123975+1)/3) 51100 1) 700 = true by decide +kernel)

private theorem r113037_51801 : RangeCond 113037 113061 51801 52501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 122575
    (51801) (powMod (2^122575) 21 ((2^122575+1)/3) 51800 1) 700 = true by decide +kernel)

private theorem r113037_52501 : RangeCond 113037 113061 52501 53201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 121175
    (52501) (powMod (2^121175) 21 ((2^121175+1)/3) 52500 1) 700 = true by decide +kernel)

private theorem r113037_53201 : RangeCond 113037 113061 53201 53901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 119775
    (53201) (powMod (2^119775) 21 ((2^119775+1)/3) 53200 1) 700 = true by decide +kernel)

private theorem r113037_53901 : RangeCond 113037 113061 53901 54601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 118375
    (53901) (powMod (2^118375) 21 ((2^118375+1)/3) 53900 1) 700 = true by decide +kernel)

private theorem r113037_54601 : RangeCond 113037 113061 54601 55301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 116975
    (54601) (powMod (2^116975) 21 ((2^116975+1)/3) 54600 1) 700 = true by decide +kernel)

private theorem r113037_55301 : RangeCond 113037 113061 55301 56001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 115575
    (55301) (powMod (2^115575) 21 ((2^115575+1)/3) 55300 1) 700 = true by decide +kernel)

private theorem r113037_56001 : RangeCond 113037 113061 56001 56701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 114175
    (56001) (powMod (2^114175) 21 ((2^114175+1)/3) 56000 1) 700 = true by decide +kernel)

private theorem r113037_56701 : RangeCond 113037 113061 56701 57401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 112775
    (56701) (powMod (2^112775) 21 ((2^112775+1)/3) 56700 1) 700 = true by decide +kernel)

private theorem r113037_57401 : RangeCond 113037 113061 57401 58101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 111375
    (57401) (powMod (2^111375) 21 ((2^111375+1)/3) 57400 1) 700 = true by decide +kernel)

private theorem r113037_58101 : RangeCond 113037 113061 58101 58801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 109975
    (58101) (powMod (2^109975) 21 ((2^109975+1)/3) 58100 1) 700 = true by decide +kernel)

private theorem r113037_58801 : RangeCond 113037 113061 58801 59501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 108575
    (58801) (powMod (2^108575) 21 ((2^108575+1)/3) 58800 1) 700 = true by decide +kernel)

private theorem r113037_59501 : RangeCond 113037 113061 59501 60201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 107175
    (59501) (powMod (2^107175) 21 ((2^107175+1)/3) 59500 1) 700 = true by decide +kernel)

private theorem r113037_60201 : RangeCond 113037 113061 60201 60901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 105775
    (60201) (powMod (2^105775) 21 ((2^105775+1)/3) 60200 1) 700 = true by decide +kernel)

private theorem r113037_60901 : RangeCond 113037 113061 60901 61601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 104375
    (60901) (powMod (2^104375) 21 ((2^104375+1)/3) 60900 1) 700 = true by decide +kernel)

private theorem r113037_61601 : RangeCond 113037 113061 61601 62301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 102975
    (61601) (powMod (2^102975) 21 ((2^102975+1)/3) 61600 1) 700 = true by decide +kernel)

private theorem r113037_62301 : RangeCond 113037 113061 62301 63001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 101575
    (62301) (powMod (2^101575) 21 ((2^101575+1)/3) 62300 1) 700 = true by decide +kernel)

private theorem r113037_63001 : RangeCond 113037 113061 63001 63701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 100175
    (63001) (powMod (2^100175) 21 ((2^100175+1)/3) 63000 1) 700 = true by decide +kernel)

private theorem r113037_63701 : RangeCond 113037 113061 63701 64401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 98775
    (63701) (powMod (2^98775) 21 ((2^98775+1)/3) 63700 1) 700 = true by decide +kernel)

private theorem r113037_64401 : RangeCond 113037 113061 64401 65101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 97375
    (64401) (powMod (2^97375) 21 ((2^97375+1)/3) 64400 1) 700 = true by decide +kernel)

private theorem r113037_65101 : RangeCond 113037 113061 65101 65801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 95975
    (65101) (powMod (2^95975) 21 ((2^95975+1)/3) 65100 1) 700 = true by decide +kernel)

private theorem r113037_65801 : RangeCond 113037 113061 65801 66501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 94575
    (65801) (powMod (2^94575) 21 ((2^94575+1)/3) 65800 1) 700 = true by decide +kernel)

private theorem r113037_66501 : RangeCond 113037 113061 66501 67201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 93175
    (66501) (powMod (2^93175) 21 ((2^93175+1)/3) 66500 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 67200"

private theorem r113037_67201 : RangeCond 113037 113061 67201 67901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 91775
    (67201) (powMod (2^91775) 21 ((2^91775+1)/3) 67200 1) 700 = true by decide +kernel)

private theorem r113037_67901 : RangeCond 113037 113061 67901 68601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 90375
    (67901) (powMod (2^90375) 21 ((2^90375+1)/3) 67900 1) 700 = true by decide +kernel)

private theorem r113037_68601 : RangeCond 113037 113061 68601 69301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 88975
    (68601) (powMod (2^88975) 21 ((2^88975+1)/3) 68600 1) 700 = true by decide +kernel)

private theorem r113037_69301 : RangeCond 113037 113061 69301 70001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 87575
    (69301) (powMod (2^87575) 21 ((2^87575+1)/3) 69300 1) 700 = true by decide +kernel)

private theorem r113037_70001 : RangeCond 113037 113061 70001 70701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 86175
    (70001) (powMod (2^86175) 21 ((2^86175+1)/3) 70000 1) 700 = true by decide +kernel)

private theorem r113037_70701 : RangeCond 113037 113061 70701 71401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 84775
    (70701) (powMod (2^84775) 21 ((2^84775+1)/3) 70700 1) 700 = true by decide +kernel)

private theorem r113037_71401 : RangeCond 113037 113061 71401 72101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 83375
    (71401) (powMod (2^83375) 21 ((2^83375+1)/3) 71400 1) 700 = true by decide +kernel)

private theorem r113037_72101 : RangeCond 113037 113061 72101 72801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 81975
    (72101) (powMod (2^81975) 21 ((2^81975+1)/3) 72100 1) 700 = true by decide +kernel)

private theorem r113037_72801 : RangeCond 113037 113061 72801 73501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 80575
    (72801) (powMod (2^80575) 21 ((2^80575+1)/3) 72800 1) 700 = true by decide +kernel)

private theorem r113037_73501 : RangeCond 113037 113061 73501 74201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 79175
    (73501) (powMod (2^79175) 21 ((2^79175+1)/3) 73500 1) 700 = true by decide +kernel)

private theorem r113037_74201 : RangeCond 113037 113061 74201 74901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 77775
    (74201) (powMod (2^77775) 21 ((2^77775+1)/3) 74200 1) 700 = true by decide +kernel)

private theorem r113037_74901 : RangeCond 113037 113061 74901 75601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 76375
    (74901) (powMod (2^76375) 21 ((2^76375+1)/3) 74900 1) 700 = true by decide +kernel)

private theorem r113037_75601 : RangeCond 113037 113061 75601 76301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 74975
    (75601) (powMod (2^74975) 21 ((2^74975+1)/3) 75600 1) 700 = true by decide +kernel)

private theorem r113037_76301 : RangeCond 113037 113061 76301 77001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 73575
    (76301) (powMod (2^73575) 21 ((2^73575+1)/3) 76300 1) 700 = true by decide +kernel)

private theorem r113037_77001 : RangeCond 113037 113061 77001 77701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 72175
    (77001) (powMod (2^72175) 21 ((2^72175+1)/3) 77000 1) 700 = true by decide +kernel)

private theorem r113037_77701 : RangeCond 113037 113061 77701 78401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 70775
    (77701) (powMod (2^70775) 21 ((2^70775+1)/3) 77700 1) 700 = true by decide +kernel)

private theorem r113037_78401 : RangeCond 113037 113061 78401 79101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 69375
    (78401) (powMod (2^69375) 21 ((2^69375+1)/3) 78400 1) 700 = true by decide +kernel)

private theorem r113037_79101 : RangeCond 113037 113061 79101 79801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 67975
    (79101) (powMod (2^67975) 21 ((2^67975+1)/3) 79100 1) 700 = true by decide +kernel)

private theorem r113037_79801 : RangeCond 113037 113061 79801 80501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 66575
    (79801) (powMod (2^66575) 21 ((2^66575+1)/3) 79800 1) 700 = true by decide +kernel)

private theorem r113037_80501 : RangeCond 113037 113061 80501 81201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 65175
    (80501) (powMod (2^65175) 21 ((2^65175+1)/3) 80500 1) 700 = true by decide +kernel)

private theorem r113037_81201 : RangeCond 113037 113061 81201 81901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 63775
    (81201) (powMod (2^63775) 21 ((2^63775+1)/3) 81200 1) 700 = true by decide +kernel)

private theorem r113037_81901 : RangeCond 113037 113061 81901 82601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 62375
    (81901) (powMod (2^62375) 21 ((2^62375+1)/3) 81900 1) 700 = true by decide +kernel)

private theorem r113037_82601 : RangeCond 113037 113061 82601 83301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 60975
    (82601) (powMod (2^60975) 21 ((2^60975+1)/3) 82600 1) 700 = true by decide +kernel)

private theorem r113037_83301 : RangeCond 113037 113061 83301 84001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 59575
    (83301) (powMod (2^59575) 21 ((2^59575+1)/3) 83300 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 84000"

private theorem r113037_84001 : RangeCond 113037 113061 84001 84701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 58175
    (84001) (powMod (2^58175) 21 ((2^58175+1)/3) 84000 1) 700 = true by decide +kernel)

private theorem r113037_84701 : RangeCond 113037 113061 84701 85401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 56775
    (84701) (powMod (2^56775) 21 ((2^56775+1)/3) 84700 1) 700 = true by decide +kernel)

private theorem r113037_85401 : RangeCond 113037 113061 85401 86101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 55375
    (85401) (powMod (2^55375) 21 ((2^55375+1)/3) 85400 1) 700 = true by decide +kernel)

private theorem r113037_86101 : RangeCond 113037 113061 86101 86801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 53975
    (86101) (powMod (2^53975) 21 ((2^53975+1)/3) 86100 1) 700 = true by decide +kernel)

private theorem r113037_86801 : RangeCond 113037 113061 86801 87501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 52575
    (86801) (powMod (2^52575) 21 ((2^52575+1)/3) 86800 1) 700 = true by decide +kernel)

private theorem r113037_87501 : RangeCond 113037 113061 87501 88201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 51175
    (87501) (powMod (2^51175) 21 ((2^51175+1)/3) 87500 1) 700 = true by decide +kernel)

private theorem r113037_88201 : RangeCond 113037 113061 88201 88901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 49775
    (88201) (powMod (2^49775) 21 ((2^49775+1)/3) 88200 1) 700 = true by decide +kernel)

private theorem r113037_88901 : RangeCond 113037 113061 88901 89601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 48375
    (88901) (powMod (2^48375) 21 ((2^48375+1)/3) 88900 1) 700 = true by decide +kernel)

private theorem r113037_89601 : RangeCond 113037 113061 89601 90301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 46975
    (89601) (powMod (2^46975) 21 ((2^46975+1)/3) 89600 1) 700 = true by decide +kernel)

private theorem r113037_90301 : RangeCond 113037 113061 90301 91001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 45575
    (90301) (powMod (2^45575) 21 ((2^45575+1)/3) 90300 1) 700 = true by decide +kernel)

private theorem r113037_91001 : RangeCond 113037 113061 91001 91701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 44175
    (91001) (powMod (2^44175) 21 ((2^44175+1)/3) 91000 1) 700 = true by decide +kernel)

private theorem r113037_91701 : RangeCond 113037 113061 91701 92401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 42775
    (91701) (powMod (2^42775) 21 ((2^42775+1)/3) 91700 1) 700 = true by decide +kernel)

private theorem r113037_92401 : RangeCond 113037 113061 92401 93101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 41375
    (92401) (powMod (2^41375) 21 ((2^41375+1)/3) 92400 1) 700 = true by decide +kernel)

private theorem r113037_93101 : RangeCond 113037 113061 93101 93801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 39975
    (93101) (powMod (2^39975) 21 ((2^39975+1)/3) 93100 1) 700 = true by decide +kernel)

private theorem r113037_93801 : RangeCond 113037 113061 93801 94501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 38575
    (93801) (powMod (2^38575) 21 ((2^38575+1)/3) 93800 1) 700 = true by decide +kernel)

private theorem r113037_94501 : RangeCond 113037 113061 94501 95201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 37175
    (94501) (powMod (2^37175) 21 ((2^37175+1)/3) 94500 1) 700 = true by decide +kernel)

private theorem r113037_95201 : RangeCond 113037 113061 95201 95901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 35775
    (95201) (powMod (2^35775) 21 ((2^35775+1)/3) 95200 1) 700 = true by decide +kernel)

private theorem r113037_95901 : RangeCond 113037 113061 95901 96601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 34375
    (95901) (powMod (2^34375) 21 ((2^34375+1)/3) 95900 1) 700 = true by decide +kernel)

private theorem r113037_96601 : RangeCond 113037 113061 96601 97301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 32975
    (96601) (powMod (2^32975) 21 ((2^32975+1)/3) 96600 1) 700 = true by decide +kernel)

private theorem r113037_97301 : RangeCond 113037 113061 97301 98001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 31575
    (97301) (powMod (2^31575) 21 ((2^31575+1)/3) 97300 1) 700 = true by decide +kernel)

private theorem r113037_98001 : RangeCond 113037 113061 98001 98701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 30175
    (98001) (powMod (2^30175) 21 ((2^30175+1)/3) 98000 1) 700 = true by decide +kernel)

private theorem r113037_98701 : RangeCond 113037 113061 98701 99401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 28775
    (98701) (powMod (2^28775) 21 ((2^28775+1)/3) 98700 1) 700 = true by decide +kernel)

private theorem r113037_99401 : RangeCond 113037 113061 99401 100101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 27375
    (99401) (powMod (2^27375) 21 ((2^27375+1)/3) 99400 1) 700 = true by decide +kernel)

private theorem r113037_100101 : RangeCond 113037 113061 100101 100801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 25975
    (100101) (powMod (2^25975) 21 ((2^25975+1)/3) 100100 1) 700 = true by decide +kernel)

#eval IO.println "N = 113037, checked through 100800"

private theorem r113037_100801 : RangeCond 113037 113061 100801 101501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 24575
    (100801) (powMod (2^24575) 21 ((2^24575+1)/3) 100800 1) 700 = true by decide +kernel)

private theorem r113037_101501 : RangeCond 113037 113061 101501 102201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 23175
    (101501) (powMod (2^23175) 21 ((2^23175+1)/3) 101500 1) 700 = true by decide +kernel)

private theorem r113037_102201 : RangeCond 113037 113061 102201 102901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 21775
    (102201) (powMod (2^21775) 21 ((2^21775+1)/3) 102200 1) 700 = true by decide +kernel)

private theorem r113037_102901 : RangeCond 113037 113061 102901 103601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 20375
    (102901) (powMod (2^20375) 21 ((2^20375+1)/3) 102900 1) 700 = true by decide +kernel)

private theorem r113037_103601 : RangeCond 113037 113061 103601 104301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 18975
    (103601) (powMod (2^18975) 21 ((2^18975+1)/3) 103600 1) 700 = true by decide +kernel)

private theorem r113037_104301 : RangeCond 113037 113061 104301 105001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 17575
    (104301) (powMod (2^17575) 21 ((2^17575+1)/3) 104300 1) 700 = true by decide +kernel)

private theorem r113037_105001 : RangeCond 113037 113061 105001 105701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 16175
    (105001) (powMod (2^16175) 21 ((2^16175+1)/3) 105000 1) 700 = true by decide +kernel)

private theorem r113037_105701 : RangeCond 113037 113061 105701 106401 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 14775
    (105701) (powMod (2^14775) 21 ((2^14775+1)/3) 105700 1) 700 = true by decide +kernel)

private theorem r113037_106401 : RangeCond 113037 113061 106401 107101 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 13375
    (106401) (powMod (2^13375) 21 ((2^13375+1)/3) 106400 1) 700 = true by decide +kernel)

private theorem r113037_107101 : RangeCond 113037 113061 107101 107801 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 11975
    (107101) (powMod (2^11975) 21 ((2^11975+1)/3) 107100 1) 700 = true by decide +kernel)

private theorem r113037_107801 : RangeCond 113037 113061 107801 108501 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 10575
    (107801) (powMod (2^10575) 21 ((2^10575+1)/3) 107800 1) 700 = true by decide +kernel)

private theorem r113037_108501 : RangeCond 113037 113061 108501 109201 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 9175
    (108501) (powMod (2^9175) 21 ((2^9175+1)/3) 108500 1) 700 = true by decide +kernel)

private theorem r113037_109201 : RangeCond 113037 113061 109201 109901 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 7775
    (109201) (powMod (2^7775) 21 ((2^7775+1)/3) 109200 1) 700 = true by decide +kernel)

private theorem r113037_109901 : RangeCond 113037 113061 109901 110601 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 6375
    (109901) (powMod (2^6375) 21 ((2^6375+1)/3) 109900 1) 700 = true by decide +kernel)

private theorem r113037_110601 : RangeCond 113037 113061 110601 111301 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 4975
    (110601) (powMod (2^4975) 21 ((2^4975+1)/3) 110600 1) 700 = true by decide +kernel)

private theorem r113037_111301 : RangeCond 113037 113061 111301 112001 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 3575
    (111301) (powMod (2^3575) 21 ((2^3575+1)/3) 111300 1) 700 = true by decide +kernel)

private theorem r113037_112001 : RangeCond 113037 113061 112001 112701 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 2175
    (112001) (powMod (2^2175) 21 ((2^2175+1)/3) 112000 1) 700 = true by decide +kernel)

private theorem r113037_112701 : RangeCond 113037 113061 112701 113038 := by
  exact reducedRange_sound (show reducedRange 113037 113061 24 775
    (112701) (powMod (2^775) 21 ((2^775+1)/3) 112700 1) 337 = true by decide +kernel)

theorem pairs113037 : AllPairs 113037 113061 := by
  apply allPairs_of_range
  exact (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_1 r113037_701) (RangeCond.trans r113037_1401 (RangeCond.trans r113037_2101 r113037_2801))) (RangeCond.trans (RangeCond.trans r113037_3501 r113037_4201) (RangeCond.trans r113037_4901 (RangeCond.trans r113037_5601 r113037_6301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_7001 r113037_7701) (RangeCond.trans r113037_8401 (RangeCond.trans r113037_9101 r113037_9801))) (RangeCond.trans (RangeCond.trans r113037_10501 r113037_11201) (RangeCond.trans r113037_11901 (RangeCond.trans r113037_12601 r113037_13301))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_14001 r113037_14701) (RangeCond.trans r113037_15401 (RangeCond.trans r113037_16101 r113037_16801))) (RangeCond.trans (RangeCond.trans r113037_17501 r113037_18201) (RangeCond.trans r113037_18901 (RangeCond.trans r113037_19601 r113037_20301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_21001 r113037_21701) (RangeCond.trans r113037_22401 (RangeCond.trans r113037_23101 r113037_23801))) (RangeCond.trans (RangeCond.trans r113037_24501 r113037_25201) (RangeCond.trans r113037_25901 (RangeCond.trans r113037_26601 r113037_27301)))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_28001 r113037_28701) (RangeCond.trans r113037_29401 (RangeCond.trans r113037_30101 r113037_30801))) (RangeCond.trans (RangeCond.trans r113037_31501 r113037_32201) (RangeCond.trans r113037_32901 (RangeCond.trans r113037_33601 r113037_34301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_35001 r113037_35701) (RangeCond.trans r113037_36401 (RangeCond.trans r113037_37101 r113037_37801))) (RangeCond.trans (RangeCond.trans r113037_38501 r113037_39201) (RangeCond.trans r113037_39901 (RangeCond.trans r113037_40601 r113037_41301))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_42001 r113037_42701) (RangeCond.trans r113037_43401 (RangeCond.trans r113037_44101 r113037_44801))) (RangeCond.trans (RangeCond.trans r113037_45501 r113037_46201) (RangeCond.trans r113037_46901 (RangeCond.trans r113037_47601 r113037_48301)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_49001 r113037_49701) (RangeCond.trans r113037_50401 (RangeCond.trans r113037_51101 r113037_51801))) (RangeCond.trans (RangeCond.trans r113037_52501 (RangeCond.trans r113037_53201 r113037_53901)) (RangeCond.trans r113037_54601 (RangeCond.trans r113037_55301 r113037_56001))))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_56701 r113037_57401) (RangeCond.trans r113037_58101 (RangeCond.trans r113037_58801 r113037_59501))) (RangeCond.trans (RangeCond.trans r113037_60201 r113037_60901) (RangeCond.trans r113037_61601 (RangeCond.trans r113037_62301 r113037_63001)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_63701 r113037_64401) (RangeCond.trans r113037_65101 (RangeCond.trans r113037_65801 r113037_66501))) (RangeCond.trans (RangeCond.trans r113037_67201 r113037_67901) (RangeCond.trans r113037_68601 (RangeCond.trans r113037_69301 r113037_70001))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_70701 r113037_71401) (RangeCond.trans r113037_72101 (RangeCond.trans r113037_72801 r113037_73501))) (RangeCond.trans (RangeCond.trans r113037_74201 r113037_74901) (RangeCond.trans r113037_75601 (RangeCond.trans r113037_76301 r113037_77001)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_77701 r113037_78401) (RangeCond.trans r113037_79101 (RangeCond.trans r113037_79801 r113037_80501))) (RangeCond.trans (RangeCond.trans r113037_81201 r113037_81901) (RangeCond.trans r113037_82601 (RangeCond.trans r113037_83301 r113037_84001)))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_84701 r113037_85401) (RangeCond.trans r113037_86101 (RangeCond.trans r113037_86801 r113037_87501))) (RangeCond.trans (RangeCond.trans r113037_88201 r113037_88901) (RangeCond.trans r113037_89601 (RangeCond.trans r113037_90301 r113037_91001)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_91701 r113037_92401) (RangeCond.trans r113037_93101 (RangeCond.trans r113037_93801 r113037_94501))) (RangeCond.trans (RangeCond.trans r113037_95201 r113037_95901) (RangeCond.trans r113037_96601 (RangeCond.trans r113037_97301 r113037_98001))))) (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_98701 r113037_99401) (RangeCond.trans r113037_100101 (RangeCond.trans r113037_100801 r113037_101501))) (RangeCond.trans (RangeCond.trans r113037_102201 r113037_102901) (RangeCond.trans r113037_103601 (RangeCond.trans r113037_104301 r113037_105001)))) (RangeCond.trans (RangeCond.trans (RangeCond.trans r113037_105701 r113037_106401) (RangeCond.trans r113037_107101 (RangeCond.trans r113037_107801 r113037_108501))) (RangeCond.trans (RangeCond.trans r113037_109201 (RangeCond.trans r113037_109901 r113037_110601)) (RangeCond.trans r113037_111301 (RangeCond.trans r113037_112001 r113037_112701))))))))

#print axioms pairs113037

end Cycle108
