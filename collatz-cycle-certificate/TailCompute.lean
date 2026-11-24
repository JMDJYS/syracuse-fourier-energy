import GridReflection

/-! Equivalent short-circuit evaluation of the bit scan and fallback
checks. The structural recursion avoids building a chain of closures of
length equal to the scan width. -/

namespace Cycle108

open Collatz.TwoRise

def shortFallback (D A2 W2 c : Nat) : Nat → Nat → Bool
  | 0, mm => Nat.beq mm 0
  | f+1, mm =>
    if Nat.beq mm 0 then true else
      let pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1))
      if Nat.beq (Nat.land pt (Nat.sub pt 1)) 0 && Nat.ble 1 pt &&
          Nat.beq (Nat.land mm pt) pt && reducedDirectOK D A2 W2 c (Nat.div A2 pt) then
        shortFallback D A2 W2 c f (Nat.xor mm pt)
      else false

theorem shortFallback_eq (D A2 W2 c f mm : Nat) :
    shortFallback D A2 W2 c f mm = reducedFallbackOK D A2 W2 c f mm := by
  induction f generalizing mm with
  | zero => rfl
  | succ f ih =>
    let pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1))
    let good := Nat.beq (Nat.land pt (Nat.sub pt 1)) 0 && Nat.ble 1 pt &&
      Nat.beq (Nat.land mm pt) pt && reducedDirectOK D A2 W2 c (Nat.div A2 pt)
    change (if Nat.beq mm 0 then true else
      if good then shortFallback D A2 W2 c f (Nat.xor mm pt) else false) =
      cond (Nat.beq mm 0) true (good && reducedFallbackOK D A2 W2 c f (Nat.xor mm pt))
    cases h : Nat.beq mm 0 <;> cases h' : good <;> simp [ih]

def shortLowScan (x : Nat) : Nat → Nat → Nat
  | 0, s => s
  | f+1, s => if Nat.beq (Nat.land (Nat.shiftRight x s) 1) 1 then s
      else shortLowScan x f (Nat.add s 1)

theorem shortLowScan_eq (x f s : Nat) : shortLowScan x f s = lowScan x f s := by
  induction f generalizing s with
  | zero => rfl
  | succ f ih =>
    let b := Nat.beq (Nat.land (Nat.shiftRight x s) 1) 1
    change (if b then s else shortLowScan x f (Nat.add s 1)) =
      cond b s (lowScan x f (Nat.add s 1))
    cases b <;> simp [ih]

def shortPatternCore (D A2 W2 c E1 L M X P s : Nat) : Bool :=
  cond (Nat.blt s E1)
    (Nat.beq (Nat.land (Nat.shiftRight P s) 1) 1 && Nat.beq (Nat.mod P (Nat.pow 2 s)) 0 &&
      shortFallback D A2 W2 c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)))
    (Nat.beq P 0 && shortFallback D A2 W2 c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)))

def shortPatternOK (D A2 W2 c A E1 lmin : Nat) : Bool :=
  let L := Nat.add (Nat.sub A lmin) 1
  let P := Nat.mod (Nat.shiftRight c A) (Nat.pow 2 E1)
  shortPatternCore D A2 W2 c E1 L (Nat.sub (Nat.pow 2 L) 1) (Nat.mod c (Nat.pow 2 (Nat.add A E1))) P
    (shortLowScan P E1 0)

def shortKCore (B E1 W k0 c A D A2 W2 y t lmin : Nat) : Bool :=
  Nat.ble k0 (Nat.add B 1) && Nat.beq (Nat.land (Nat.shiftRight y t) 1) 1 &&
    reducedDirectRange D A2 W2 c (Nat.add t 1) A2 &&
    reducedDirectRange D A2 W2 c (Nat.sub (Nat.min A lmin) 1) 2 &&
    cond (Nat.ble A lmin) true (Nat.ble (Nat.add A E1) W && shortPatternOK D A2 W2 c A E1 lmin)

def shortKOK (N B E1 W k0 c : Nat) : Bool :=
  let A := cond (Nat.blt k0 N) (Nat.sub N k0) 1
  let y := Nat.shiftRight c A
  shortKCore B E1 W k0 c A (Nat.pow 2 (Nat.sub (Nat.add B 1) k0)) (Nat.pow 2 A) (Nat.pow 2 W) y
    (shortLowScan y W 0) (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1)))

def shortLoop (N B E W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let inv := updateInverse W c
      shortKOK N B E W k inv && ih (Nat.add k 1) inv) cnt

def shortRange (N B E W k c cnt : Nat) : Bool :=
  Nat.ble 1 k && Nat.beq (Nat.mod (Nat.pow 2 W) 3) 2 &&
    Nat.blt c (Nat.pow 2 W) &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 (Nat.sub k 1)) c) (Nat.pow 2 W)) 1 &&
    shortLoop N B E W cnt k c


theorem shortPatternCore_eq (D A2 W2 c E1 L M X P s : Nat) :
    shortPatternCore D A2 W2 c E1 L M X P s = reducedPatternCore D A2 W2 c E1 L M X P s := by
  simp only [shortPatternCore, reducedPatternCore, shortFallback_eq]

theorem shortPatternOK_eq (D A2 W2 c A E1 lmin : Nat) :
    shortPatternOK D A2 W2 c A E1 lmin = reducedPatternOK D A2 W2 c A E1 lmin := by
  simp only [shortPatternOK, reducedPatternOK, shortPatternCore_eq, shortLowScan_eq]

theorem shortKCore_eq (B E1 W k c A D A2 W2 y t lmin : Nat) :
    shortKCore B E1 W k c A D A2 W2 y t lmin = reducedKCore B E1 W k c A D A2 W2 y t lmin := by
  simp only [shortKCore, reducedKCore, shortPatternOK_eq]

theorem shortKOK_eq (N B E1 W k c : Nat) :
    shortKOK N B E1 W k c = reducedKOK N B E1 W k c := by
  simp only [shortKOK, reducedKOK, shortKCore_eq, shortLowScan_eq]

theorem shortLoop_eq (N B E W cnt k c : Nat) :
    shortLoop N B E W cnt k c = reducedLoop N B E W cnt k c := by
  induction cnt generalizing k c with
  | zero => rfl
  | succ cnt ih =>
    change (shortKOK N B E W k (updateInverse W c) &&
      shortLoop N B E W cnt (Nat.add k 1) (updateInverse W c)) =
      (reducedKOK N B E W k (updateInverse W c) &&
        reducedLoop N B E W cnt (Nat.add k 1) (updateInverse W c))
    rw [shortKOK_eq, ih]

theorem shortRange_eq (N B E W k c cnt : Nat) :
    shortRange N B E W k c cnt = reducedRange N B E W k c cnt := by
  simp only [shortRange, reducedRange, shortLoop_eq]

def shortChunk (N B i : Nat) : Bool :=
  let w := chunkWidth N i
  shortRange N B 24 w (chunkStart i)
    (powMod (2^w) 21 ((2^w+1)/3) (i*700) 1) (chunkSize N i)

def shortCheckAll (N B : Nat) : Bool :=
  (List.range ((N+699)/700)).all (shortChunk N B)

theorem shortCheckAll_eq (N B : Nat) : shortCheckAll N B = checkAllPairs N B := by
  unfold shortCheckAll checkAllPairs
  congr 1
  funext i
  simp only [shortChunk, checkChunk, shortRange_eq]

theorem allPairs_of_shortCheckAll {N B : Nat} (h : shortCheckAll N B = true) :
    AllPairs N B := allPairs_of_checkAllPairs ((shortCheckAll_eq N B) ▸ h)

#print axioms allPairs_of_shortCheckAll

end Cycle108
