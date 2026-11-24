import ReducedDirect

/-! A faster evaluation of the imported checker. The definitions retain
Alick's control flow and use the proved reduced residue for each direct
test. Apache-2.0, see LICENSE-Alick. -/

namespace Cycle108

open Collatz.TwoRise

def reducedDirectRange (D A2 W2 c cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih L2 => reducedDirectOK D A2 W2 c L2 && ih (Nat.mul 2 L2)) cnt

def reducedFallbackOK (D A2 W2 c f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun mm => Nat.beq mm 0)
    (fun _ ih mm => cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt && Nat.beq (Nat.land mm Pt) Pt &&
          reducedDirectOK D A2 W2 c (Nat.div A2 Pt) && ih (Nat.xor mm Pt))) f

def reducedPatternCore (D A2 W2 c E1 L M X P s : Nat) : Bool :=
  cond (Nat.blt s E1)
    (Nat.beq (Nat.land (Nat.shiftRight P s) 1) 1 && Nat.beq (Nat.mod P (Nat.pow 2 s)) 0 &&
      reducedFallbackOK D A2 W2 c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)))
    (Nat.beq P 0 && reducedFallbackOK D A2 W2 c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)))

def reducedPatternOK (D A2 W2 c A E1 lmin : Nat) : Bool :=
  let L := Nat.add (Nat.sub A lmin) 1
  let P := Nat.mod (Nat.shiftRight c A) (Nat.pow 2 E1)
  reducedPatternCore D A2 W2 c E1 L (Nat.sub (Nat.pow 2 L) 1) (Nat.mod c (Nat.pow 2 (Nat.add A E1))) P
    (lowScan P E1 0)

def reducedKCore (B E1 W k0 c A D A2 W2 y t lmin : Nat) : Bool :=
  Nat.ble k0 (Nat.add B 1) && Nat.beq (Nat.land (Nat.shiftRight y t) 1) 1 &&
    reducedDirectRange D A2 W2 c (Nat.add t 1) A2 &&
    reducedDirectRange D A2 W2 c (Nat.sub (Nat.min A lmin) 1) 2 &&
    cond (Nat.ble A lmin) true (Nat.ble (Nat.add A E1) W && reducedPatternOK D A2 W2 c A E1 lmin)

def reducedKOK (N B E1 W k0 c : Nat) : Bool :=
  let A := cond (Nat.blt k0 N) (Nat.sub N k0) 1
  let y := Nat.shiftRight c A
  reducedKCore B E1 W k0 c A (Nat.pow 2 (Nat.sub (Nat.add B 1) k0)) (Nat.pow 2 A) (Nat.pow 2 W) y
    (lowScan y W 0) (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1)))

theorem reducedDirectRange_eq (D A2 W2 c cnt L : Nat) :
    reducedDirectRange D A2 W2 c cnt L = directRange D A2 W2 c cnt L := by
  induction cnt generalizing L with
  | zero => rfl
  | succ cnt ih =>
    change (reducedDirectOK D A2 W2 c L &&
      reducedDirectRange D A2 W2 c cnt (2*L)) = _
    rw [directRange_succ, reducedDirectOK_eq, ih]
    rfl

theorem reducedFallbackOK_eq (D A2 W2 c cnt mm : Nat) :
    reducedFallbackOK D A2 W2 c cnt mm = fallbackOK D A2 W2 c cnt mm := by
  induction cnt generalizing mm with
  | zero => rfl
  | succ cnt ih =>
    have e : reducedFallbackOK D A2 W2 c (cnt+1) mm =
        cond (Nat.beq mm 0) true
          (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1))
           Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt &&
             Nat.beq (Nat.land mm Pt) Pt && reducedDirectOK D A2 W2 c (Nat.div A2 Pt) &&
             reducedFallbackOK D A2 W2 c cnt (Nat.xor mm Pt)) := rfl
    simp only [e, fallbackOK_succ, reducedDirectOK_eq, ih]

theorem reducedPatternCore_eq (D A2 W2 c E1 L M X P s : Nat) :
    reducedPatternCore D A2 W2 c E1 L M X P s = patternCore D A2 W2 c E1 L M X P s := by
  simp only [reducedPatternCore, patternCore, reducedFallbackOK_eq]

theorem reducedPatternOK_eq (D A2 W2 c A E1 lmin : Nat) :
    reducedPatternOK D A2 W2 c A E1 lmin = patternOK D A2 W2 c A E1 lmin := by
  simp only [reducedPatternOK, patternOK, reducedPatternCore_eq]

theorem reducedKCore_eq (B E1 W k c A D A2 W2 y t lmin : Nat) :
    reducedKCore B E1 W k c A D A2 W2 y t lmin = kCore B E1 W k c A D A2 W2 y t lmin := by
  simp only [reducedKCore, kCore, reducedDirectRange_eq, reducedPatternOK_eq]

theorem reducedKOK_eq (N B E1 W k c : Nat) :
    reducedKOK N B E1 W k c = kOK N B E1 W k c := by
  simp only [reducedKOK, kOK, reducedKCore_eq]

def reducedLoop (N B E W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let inv := updateInverse W c
      reducedKOK N B E W k inv && ih (Nat.add k 1) inv) cnt

theorem reducedLoop_eq (N B E W cnt k c : Nat) :
    reducedLoop N B E W cnt k c = fastLoop N B E W cnt k c := by
  induction cnt generalizing k c with
  | zero => rfl
  | succ cnt ih =>
    change (reducedKOK N B E W k (updateInverse W c) &&
      reducedLoop N B E W cnt (Nat.add k 1) (updateInverse W c)) =
      (kOK N B E W k (updateInverse W c) &&
        fastLoop N B E W cnt (Nat.add k 1) (updateInverse W c))
    rw [reducedKOK_eq, ih]

def reducedRange (N B E W k c cnt : Nat) : Bool :=
  Nat.ble 1 k && Nat.beq (Nat.mod (Nat.pow 2 W) 3) 2 &&
    Nat.blt c (Nat.pow 2 W) &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 (Nat.sub k 1)) c) (Nat.pow 2 W)) 1 &&
    reducedLoop N B E W cnt k c

theorem reducedRange_sound {N B E W k c cnt : Nat}
    (h : reducedRange N B E W k c cnt = true) : RangeCond N B k (k+cnt) := by
  apply rangeCheck_sound (E := E) (W := W) (c := c)
  simpa only [reducedRange, reducedLoop_eq, rangeCheck] using h

#print axioms reducedRange_sound

end Cycle108
