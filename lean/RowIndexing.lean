import SourceFormation
import GoodMapEmbedding
/-!
# Executable compact row and middle addresses

Good subsets are represented by filtered integer mask codes. Their compact
rank is an explicit search in that stored code sequence, and their inverse
reads a stored code before decoding its Boolean coordinates. Binary outer
and middle coordinates use explicit mixed-radix equivalences.
-/
namespace ThinMatrix.RowIndexing
open WalshEmbedding SourceFormation GoodMapEmbedding
open scoped BigOperators

def cubeEquiv (n : ℕ) : Cube n ≃ Fin (2^n) :=
  (Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm)).trans finFunctionFinEquiv

lemma cubeSupport_setBits {L : ℕ} (Q : Finset (Fin L)) : cubeSupport (setBits Q) = Q := by
  ext i
  simp [cubeSupport, setBits]

lemma setBits_cubeSupport {L : ℕ} (bits : Cube L) : setBits (cubeSupport bits) = bits := by
  funext i
  simp [setBits, cubeSupport]

/-- Actual finite integer codes; no choice of a Fintype equivalence. -/
def goodCodes (L m : ℕ) : List (Fin (2^L)) :=
  (List.finRange (2^L)).filter (fun code => decide (cubeSupport ((cubeEquiv L).symm code) ∈ goodSlots L m))

lemma goodCodes_nodup (L m : ℕ) : (goodCodes L m).Nodup :=
  (List.nodup_finRange _).filter _

lemma mem_goodCodes (L m : ℕ) (code : Fin (2^L)) :
    code ∈ goodCodes L m ↔ cubeSupport ((cubeEquiv L).symm code) ∈ goodSlots L m := by
  simp [goodCodes]

abbrev GoodSlot (L m : ℕ) := ↥(goodSlots L m)

def goodCode {L m : ℕ} (Q : GoodSlot L m) : Fin (2^L) := cubeEquiv L (setBits Q.val)

lemma goodCode_mem {L m : ℕ} (Q : GoodSlot L m) : goodCode Q ∈ goodCodes L m := by
  rw [mem_goodCodes]
  simpa only [goodCode, Equiv.symm_apply_apply, cubeSupport_setBits] using Q.property

def goodListEquiv (L m : ℕ) : GoodSlot L m ≃ Fin (goodCodes L m).length where
  toFun Q := ⟨(goodCodes L m).idxOf (goodCode Q), List.idxOf_lt_length_iff.mpr (goodCode_mem Q)⟩
  invFun i := ⟨cubeSupport ((cubeEquiv L).symm (goodCodes L m)[i.val]),
    (mem_goodCodes L m _).mp (List.getElem_mem i.isLt)⟩
  left_inv Q := by
    apply Subtype.ext
    have hi := List.idxOf_lt_length_iff.mpr (goodCode_mem Q)
    have he := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (goodCode_mem Q))
    change cubeSupport ((cubeEquiv L).symm ((goodCodes L m)[(goodCodes L m).idxOf (goodCode Q)]'hi)) = Q.val
    rw [he]
    simp only [goodCode, Equiv.symm_apply_apply, cubeSupport_setBits]
  right_inv i := by
    apply Fin.ext
    simp only [goodCode, setBits_cubeSupport, Equiv.apply_symm_apply]
    exact (goodCodes_nodup L m).idxOf_getElem i.val i.isLt

lemma goodCodes_length (L m : ℕ) : (goodCodes L m).length = (goodSlots L m).card := by
  have h := Fintype.card_congr (goodListEquiv L m)
  simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm

lemma goodCodes_length_le (L m : ℕ) : (goodCodes L m).length ≤ 2^L := by
  exact (List.length_filter_le _ _).trans_eq (show (List.finRange (2^L)).length = 2^L from List.length_finRange)

def goodRankEquiv (L m : ℕ) : GoodSlot L m ≃ Fin (goodSlots L m).card :=
  (goodListEquiv L m).trans (finCongr (goodCodes_length L m))

def cubePairEquiv (n : ℕ) : (Cube n × Cube n) ≃ Fin (4^n) :=
  ((cubeEquiv n).prodCongr (cubeEquiv n)).trans
    (finProdFinEquiv.trans (finCongr (by rw [← mul_pow]; norm_num)))

abbrev OuterIndex (L m : ℕ) := GoodSlot L m × (Cube (L-m) × Cube (L-m))
def rowEquiv (L m : ℕ) : OuterIndex L m ≃ Fin ((goodSlots L m).card * 4^(L-m)) :=
  ((goodRankEquiv L m).prodCongr (cubePairEquiv (L-m))).trans finProdFinEquiv

theorem cubeEquiv_val (n : ℕ) (bits : Cube n) :
    (cubeEquiv n bits).val = ∑ i : Fin n, (finTwoEquiv.symm (bits i)).val * 2^i.val := by
  exact finFunctionFinEquiv_apply _

theorem cubePairEquiv_val (n : ℕ) (a b : Cube n) :
    (cubePairEquiv n (a,b)).val = (cubeEquiv n a).val*2^n + (cubeEquiv n b).val := by
  simp [cubePairEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem rowEquiv_val (L m : ℕ) (row : OuterIndex L m) :
    (rowEquiv L m row).val =
      (goodRankEquiv L m row.1).val*4^(L-m) +
        (cubeEquiv (L-m) row.2.1).val*2^(L-m) + (cubeEquiv (L-m) row.2.2).val := by
  change (cubePairEquiv (L-m) (row.2.1,row.2.2)).val +
    4^(L-m)*(goodRankEquiv L m row.1).val = _
  rw [cubePairEquiv_val]
  ring

theorem cubePairEquiv_inverse_fst (n : ℕ) (i : Fin (4^n)) :
    (cubeEquiv n ((cubePairEquiv n).symm i).1).val = i.val / 2^n := by
  simp [cubePairEquiv, finProdFinEquiv]

theorem cubePairEquiv_inverse_snd (n : ℕ) (i : Fin (4^n)) :
    (cubeEquiv n ((cubePairEquiv n).symm i).2).val = i.val % 2^n := by
  simp [cubePairEquiv, finProdFinEquiv]

/-- A stored compact good-code array, prepared once and reused by every
row-address calculation. Inverse access uses one actual vector read. -/
structure GoodIndexStore (L m : ℕ) where
  codes : Vector (Fin (2^L)) (goodSlots L m).card
  correct : codes.toList = goodCodes L m

def prepareGoodIndexStore (L m : ℕ) : GoodIndexStore L m where
  codes := ⟨(goodCodes L m).toArray, by simp [goodCodes_length]⟩
  correct := by simp

/-- Literal linear code search. Every skipped code adds one to the returned
rank; equality is integer equality on an L-bit mask code. -/
def scanCode (L : ℕ) (target : Fin (2^L)) : List (Fin (2^L)) → Program ℕ
  | [] => ⟨0, 1⟩
  | code :: codes =>
      if code = target then ⟨0, 4*(L+1)⟩
      else let tail := scanCode L target codes
           ⟨tail.value+1, tail.operations+4*(L+1)⟩

theorem scanCode_value (L : ℕ) (target : Fin (2^L)) (codes : List (Fin (2^L))) :
    (scanCode L target codes).value = codes.idxOf target := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
      by_cases h : code = target
      · simp [scanCode, h]
      · simp [scanCode, h, ih]

theorem scanCode_cost (L : ℕ) (target : Fin (2^L)) (codes : List (Fin (2^L))) :
    (scanCode L target codes).operations ≤ 4*(L+1)*(codes.length+1) := by
  induction codes with
  | nil => simp [scanCode]; omega
  | cons code codes ih =>
      by_cases h : code = target
      · simp only [scanCode, h, if_true, List.length_cons]
        nlinarith
      · simp only [scanCode, h, if_false, List.length_cons]
        nlinarith

/-- Forward good-set address scans the already stored array, rather than
reconstructing the good family for each raw-source table entry. -/
def goodRankProgram {L m : ℕ} (store : GoodIndexStore L m) (Q : GoodSlot L m) :
    Program (Fin (goodSlots L m).card) :=
  let scanned := scanCode L (goodCode Q) store.codes.toList
  { value := ⟨scanned.value, by
      rw [scanCode_value, store.correct]
      simpa only [goodCodes_length] using
        List.idxOf_lt_length_iff.mpr (goodCode_mem Q)⟩
    -- Copying stored codes to the scan list and forming the mask key are charged.
    operations := scanned.operations + 4*store.codes.toArray.size + 4*(L+1)^2 }

theorem goodRankProgram_value {L m : ℕ} (store : GoodIndexStore L m) (Q : GoodSlot L m) :
    (goodRankProgram store Q).value = goodRankEquiv L m Q := by
  apply Fin.ext
  simp [goodRankProgram, scanCode_value, store.correct, goodRankEquiv, goodListEquiv]

theorem goodRankProgram_cost {L m : ℕ} (store : GoodIndexStore L m) (Q : GoodSlot L m) :
    (goodRankProgram store Q).operations ≤ 16*(L+1)^2*(2^L+1) := by
  have hs := scanCode_cost L (goodCode Q) store.codes.toList
  have hl : store.codes.toList.length ≤ 2^L := by
    rw [store.correct]
    exact goodCodes_length_le L m
  have hc : (goodSlots L m).card ≤ 2^L := by
    rw [← goodCodes_length]
    exact goodCodes_length_le L m
  dsimp only [goodRankProgram]
  rw [Vector.size_toArray]
  nlinarith [Nat.zero_le ((L+1)^2), Nat.zero_le (2^L),
    Nat.mul_le_mul_left (4*(L+1)) (Nat.add_le_add_right hl 1)]

/-- An executable binary rank loop reads each input Boolean once. -/
def cubeRankNatProgram : (n : ℕ) → Cube n → Program ℕ
  | 0, _ => ⟨0, 1⟩
  | n+1, bits =>
      let tail := cubeRankNatProgram n (fun i => bits i.succ)
      ⟨(finTwoEquiv.symm (bits 0)).val + 2*tail.value, tail.operations+5⟩

theorem cubeRankNatProgram_value (n : ℕ) (bits : Cube n) :
    (cubeRankNatProgram n bits).value = (cubeEquiv n bits).val := by
  induction n with
  | zero => simp [cubeRankNatProgram]
  | succ n ih =>
      simp only [cubeRankNatProgram, ih, cubeEquiv_val, Fin.sum_univ_succ,
        Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem cubeRankNatProgram_cost (n : ℕ) (bits : Cube n) :
    (cubeRankNatProgram n bits).operations = 5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cubeRankNatProgram, ih]; omega

/-- The returned finite rank carries the bound proved for the explicit loop. -/
def cubeRankProgram (n : ℕ) (bits : Cube n) : Program (Fin (2^n)) :=
  let rank := cubeRankNatProgram n bits
  ⟨⟨rank.value, by rw [cubeRankNatProgram_value]; exact (cubeEquiv n bits).isLt⟩,
    rank.operations+1⟩

theorem cubeRankProgram_value (n : ℕ) (bits : Cube n) :
    (cubeRankProgram n bits).value = cubeEquiv n bits := by
  apply Fin.ext
  exact cubeRankNatProgram_value n bits

theorem cubeRankProgram_cost (n : ℕ) (bits : Cube n) :
    (cubeRankProgram n bits).operations = 5*n+2 := by
  simp only [cubeRankProgram, cubeRankNatProgram_cost]

/-- The inverse good-set locator reads exactly one stored code. -/
def goodUnrank {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : GoodSlot L m :=
  ⟨cubeSupport ((cubeEquiv L).symm (store.codes.get i)), by
    apply (mem_goodCodes L m _).mp
    rw [← store.correct]
    apply Vector.mem_toList_iff.mpr
    exact Vector.getElem_mem i.isLt⟩

theorem goodUnrank_value {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : goodUnrank store i = (goodRankEquiv L m).symm i := by
  apply Subtype.ext
  change cubeSupport ((cubeEquiv L).symm (store.codes.get i)) =
    cubeSupport ((cubeEquiv L).symm ((goodCodes L m)[i.val]'(by rw [goodCodes_length]; exact i.isLt)))
  congr 2
  have hl : i.val < store.codes.toList.length := by simp
  have he := Vector.getElem_toList (xs := store.codes) hl
  simpa [Vector.get, store.correct] using he.symm

@[simp] theorem goodUnrank_rank {L m : ℕ} (store : GoodIndexStore L m) (Q : GoodSlot L m) :
    goodUnrank store (goodRankProgram store Q).value = Q := by
  rw [goodRankProgram_value, goodUnrank_value]
  exact (goodRankEquiv L m).symm_apply_apply Q

@[simp] theorem goodRank_unrank {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : (goodRankProgram store (goodUnrank store i)).value = i := by
  rw [goodRankProgram_value, goodUnrank_value]
  exact (goodRankEquiv L m).apply_symm_apply i

/-- A compact row is decoded by quotient/remainder, one stored good-code
read, and the two explicit binary inverse maps. -/
def rowUnrank {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin ((goodSlots L m).card*4^(L-m))) : OuterIndex L m :=
  (goodUnrank store (finProdFinEquiv.symm i).1,
    (cubePairEquiv (L-m)).symm (finProdFinEquiv.symm i).2)

theorem rowUnrank_value {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin ((goodSlots L m).card*4^(L-m))) : rowUnrank store i = (rowEquiv L m).symm i := by
  unfold rowUnrank
  rw [goodUnrank_value]
  rfl

/-- Runtime row decoding divides only by the fixed binary-coordinate width;
the good-family cardinality appears solely in erased finite bounds. -/
theorem rowUnrank_good_rank {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin ((goodSlots L m).card*4^(L-m))) :
    (goodRankEquiv L m (rowUnrank store i).1).val = i.val / 4^(L-m) := by
  simp [rowUnrank, goodUnrank_value, finProdFinEquiv]

theorem rowUnrank_cube_rank {L m : ℕ} (store : GoodIndexStore L m)
    (i : Fin ((goodSlots L m).card*4^(L-m))) :
    (cubePairEquiv (L-m) (rowUnrank store i).2).val = i.val % 4^(L-m) := by
  simp [rowUnrank, finProdFinEquiv]

/-- Combining the stored good rank and two literal binary loops gives the
same row-major address as the explicit compact equivalence. -/
def rowRankProgram {L m : ℕ} (store : GoodIndexStore L m) (row : OuterIndex L m) :
    Program (Fin ((goodSlots L m).card*4^(L-m))) :=
  let good := goodRankProgram store row.1
  let first := cubeRankProgram (L-m) row.2.1
  let second := cubeRankProgram (L-m) row.2.2
  let paired : Fin (4^(L-m)) := Fin.cast (by rw [← mul_pow]; norm_num)
    (finProdFinEquiv (first.value,second.value))
  ⟨finProdFinEquiv (good.value,paired),
    good.operations+first.operations+second.operations+6⟩

theorem rowRankProgram_value {L m : ℕ} (store : GoodIndexStore L m) (row : OuterIndex L m) :
    (rowRankProgram store row).value = rowEquiv L m row := by
  simp only [rowRankProgram, goodRankProgram_value, cubeRankProgram_value]
  rfl

theorem rowRankProgram_cost {L m : ℕ} (store : GoodIndexStore L m) (row : OuterIndex L m) :
    (rowRankProgram store row).operations ≤ 32*(L+1)^2*(2^L+1) := by
  have hg := goodRankProgram_cost store row.1
  dsimp only [rowRankProgram]
  rw [cubeRankProgram_cost, cubeRankProgram_cost]
  have hk : L-m ≤ L := Nat.sub_le _ _
  have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by norm_num)
  nlinarith [Nat.zero_le ((L+1)^2)]

/-- The literal middle locator uses two binary loops and mixed-radix pairing. -/
def middleRankProgram (m : ℕ) (inner : Cube m × Cube m) : Program (Fin (4^m)) :=
  let first := cubeRankProgram m inner.1
  let second := cubeRankProgram m inner.2
  ⟨Fin.cast (by rw [← mul_pow]; norm_num) (finProdFinEquiv (first.value,second.value)),
    first.operations+second.operations+4⟩

theorem middleRankProgram_value (m : ℕ) (inner : Cube m × Cube m) :
    (middleRankProgram m inner).value = cubePairEquiv m inner := by
  simp only [middleRankProgram, cubeRankProgram_value]
  rfl

theorem middleRankProgram_cost (m : ℕ) (inner : Cube m × Cube m) :
    (middleRankProgram m inner).operations = 10*m+8 := by
  simp only [middleRankProgram, cubeRankProgram_cost]
  omega

/-- Recover the actual outer length from the original backing storage.
The semantic vector length occurs only in erased bounds. -/
def originalOuterSize {α : Type*} {len : ℕ} (m : ℕ) (data : Vector α len) : ℕ :=
  data.toArray.size / 4^m

theorem originalOuterSize_left {α : Type*} {N m : ℕ} (data : Vector α (N*4^m)) :
    originalOuterSize m data = N := by
  rw [originalOuterSize, Vector.size_toArray, Nat.mul_div_cancel _ (by positivity)]

theorem originalOuterSize_right {α : Type*} {N m : ℕ} (data : Vector α (4^m*N)) :
    originalOuterSize m data = N := by
  rw [originalOuterSize, Vector.size_toArray, Nat.mul_div_cancel_left _ (by positivity)]

/-- A padded compact left input uses only stored array lengths in its runtime
stride, comparison and original row-major backing-array address. -/
def readOriginalLeftProgram {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) : Program ℤ :=
  let outer := rowRankProgram store row
  let middle := middleRankProgram m inner
  let v := band*(store.codes.toArray.size*4^(L-m)) + outer.value.val
  if hv : v < originalOuterSize m data then
    let address : Fin (N*4^m) := ⟨middle.value.val+4^m*v, by
      have hvN : v < N := by simpa only [originalOuterSize_left] using hv
      have hm := middle.value.isLt
      nlinarith [Nat.mul_le_mul_right (4^m) (Nat.succ_le_of_lt hvN)]⟩
    ⟨(data.get address).get target, outer.operations+middle.operations+12⟩
  else ⟨0, outer.operations+middle.operations+12⟩

/-- The right input uses its stored outer length in the transpose row-major
D-by-N address, rather than evaluating the semantic N parameter. -/
def readOriginalRightProgram {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) : Program ℤ :=
  let outer := rowRankProgram store col
  let middle := middleRankProgram m inner
  let cachedOuter := originalOuterSize m data
  let v := band*(store.codes.toArray.size*4^(L-m)) + outer.value.val
  if hv : v < cachedOuter then
    let address : Fin (4^m*N) := ⟨v+cachedOuter*middle.value.val, by
      have hN : cachedOuter = N := originalOuterSize_right data
      have hvN : v < N := by simpa only [hN] using hv
      have hm := middle.value.isLt
      rw [hN]
      nlinarith [Nat.mul_le_mul_left N (Nat.succ_le_of_lt hm)]⟩
    ⟨(data.get address).get target, outer.operations+middle.operations+12⟩
  else ⟨0, outer.operations+middle.operations+12⟩

theorem readOriginalLeftProgram_value {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) :
    (readOriginalLeftProgram store data band row inner target).value =
      let v := band*((goodSlots L m).card*4^(L-m)) + (rowEquiv L m row).val
      if hv : v < N then
        (data.get (finProdFinEquiv (⟨v,hv⟩,cubePairEquiv m inner))).get target else 0 := by
  simp only [readOriginalLeftProgram, rowRankProgram_value, middleRankProgram_value,
    Vector.size_toArray, originalOuterSize_left]
  split <;> rfl

theorem readOriginalRightProgram_value {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) :
    (readOriginalRightProgram store data band inner col target).value =
      let v := band*((goodSlots L m).card*4^(L-m)) + (rowEquiv L m col).val
      if hv : v < N then
        (data.get (finProdFinEquiv (cubePairEquiv m inner,⟨v,hv⟩))).get target else 0 := by
  simp only [readOriginalRightProgram, rowRankProgram_value, middleRankProgram_value,
    Vector.size_toArray, originalOuterSize_right]
  split <;> rfl

theorem readOriginalLeftProgram_cost {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (N*4^m)) (band : ℕ)
    (row : OuterIndex L m) (inner : Cube m × Cube m) (target : Fin q) (hm : m ≤ L) :
    (readOriginalLeftProgram store data band row inner target).operations ≤
      64*(L+1)^2*(2^L+1) := by
  have ho := rowRankProgram_cost store row
  have hi := middleRankProgram_cost m inner
  have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by norm_num)
  unfold readOriginalLeftProgram
  dsimp only
  split <;> dsimp only <;> rw [hi] <;> nlinarith [Nat.zero_le ((L+1)^2)]

theorem readOriginalRightProgram_cost {N L m q : ℕ} (store : GoodIndexStore L m)
    (data : Vector (Vector ℤ q) (4^m*N)) (band : ℕ)
    (inner : Cube m × Cube m) (col : OuterIndex L m) (target : Fin q) (hm : m ≤ L) :
    (readOriginalRightProgram store data band inner col target).operations ≤
      64*(L+1)^2*(2^L+1) := by
  have ho := rowRankProgram_cost store col
  have hi := middleRankProgram_cost m inner
  have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by norm_num)
  unfold readOriginalRightProgram
  dsimp only
  split <;> dsimp only <;> rw [hi] <;> nlinarith [Nat.zero_le ((L+1)^2)]

#print axioms rowEquiv
#print axioms rowEquiv_val
#print axioms goodRankProgram_value
#print axioms goodRankProgram_cost
#print axioms goodUnrank_value
#print axioms rowUnrank_value
#print axioms rowUnrank_good_rank
#print axioms rowUnrank_cube_rank
#print axioms originalOuterSize_left
#print axioms originalOuterSize_right
#print axioms rowRankProgram_value
#print axioms rowRankProgram_cost
#print axioms readOriginalLeftProgram_value
#print axioms readOriginalRightProgram_value
#print axioms readOriginalLeftProgram_cost
#print axioms readOriginalRightProgram_cost
end ThinMatrix.RowIndexing
