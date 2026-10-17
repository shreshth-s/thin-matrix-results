import Mathlib

/-!
# Algebraic components of the aligned Walsh/source embedding

All identities below hold over an arbitrary commutative ring. In particular,
they do not require division by the Boolean-cube cardinality. The full raw
A3--A4 arrays are defined on all normal/opposite words, with their genuine
good-slot and run masks. The surviving-contraction theorem evaluates actual
raw summands; it does not assume a matrix-product identity.

`RawWordBijection.lean` supplies the finite raw-to-surviving word reindexing
and composes the complete scaled embedding identity. The existence/density
of good restrictions, asymptotic preprocessing costs, and decoding by exact
integer division remain separate obligations. No division over a general
commutative ring is asserted.
-/

namespace ThinMatrix.WalshEmbedding

open scoped BigOperators

abbrev Cube (k : ℕ) := Fin k → Bool

def zeroBits (k : ℕ) : Cube k := fun _ => false

def ones {k : ℕ} (a : Cube k) : ℕ :=
  (Finset.univ.filter fun i => a i).card

theorem ones_le {k : ℕ} (a : Cube k) : ones a ≤ k := by
  simpa [ones] using Finset.card_filter_le Finset.univ (fun i : Fin k => a i)

theorem ones_eq_zero {k : ℕ} (a : Cube k) : ones a = 0 ↔ a = zeroBits k := by
  classical
  simp only [ones, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    have hi := h (Finset.mem_univ i)
    cases hb : a i <;> simp_all [zeroBits]
  · intro h
    subst a
    simp [zeroBits]

section Characters

variable {R : Type*} [CommRing R]

def bitChar (a x : Bool) : R := if a && x then -1 else 1

def character {k : ℕ} (a x : Cube k) : R :=
  ∏ i, bitChar (R := R) (a i) (x i)

theorem bit_orthogonality (x y : Bool) :
    (∑ a : Bool, bitChar (R := R) a x * bitChar (R := R) a y) =
      if x = y then (2 : R) else 0 := by
  cases x <;> cases y <;> norm_num [bitChar]

theorem character_symmetric {k : ℕ} (a x : Cube k) :
    character (R := R) a x = character (R := R) x a := by
  unfold character
  congr 1
  funext i
  cases a i <;> cases x i <;> rfl

theorem character_orthogonality {k : ℕ} (x y : Cube k) :
    (∑ a : Cube k, character (R := R) a x * character (R := R) a y) =
      if x = y then (2 : R)^k else 0 := by
  classical
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (a : Bool) =>
    bitChar (R := R) a (x i) * bitChar (R := R) a (y i))]
  simp_rw [bit_orthogonality]
  by_cases h : x = y
  · subst y
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      exact h (funext fun i => by simpa using not_exists.mp hn i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The unnormalized transform in (A2). -/
def walsh {k : ℕ} (f : Cube k → R) (z : Cube k) : R :=
  ∑ a, character (R := R) z a * f a

/-- Integer-scaled inversion, including the empty cube and all characteristics. -/
theorem walsh_inversion {k : ℕ} (f : Cube k → R) (a : Cube k) :
    walsh (walsh f) a = (2 : R)^k * f a := by
  classical
  simp only [walsh]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, character_symmetric a, character_orthogonality]
  simp

/-- A good restricted Delta map only changes the enumeration of frequencies. -/
theorem walsh_inversion_reindex {k : ℕ} {V : Type*} [Fintype V]
    (delta : V ≃ Cube k) (f : Cube k → R) (a : Cube k) :
    (∑ v, character (R := R) a (delta v) * walsh f (delta v)) =
      (2 : R)^k * f a := by
  calc
    _ = walsh (walsh f) a := delta.sum_comp _
    _ = _ := walsh_inversion f a

def xorBits {k : ℕ} (a b : Cube k) : Cube k := fun i => Bool.xor (a i) (b i)

def parity : List Bool → Bool
  | [] => false
  | b :: bs => Bool.xor b (parity bs)

def bitSign (b : Bool) : R := if b then -1 else 1

theorem sign_xor (a b : Bool) :
    bitSign (R := R) (Bool.xor a b) = bitSign (R := R) a * bitSign (R := R) b := by
  cases a <;> cases b <;> norm_num [bitSign]

theorem sign_parity (bs : List Bool) :
    bitSign (R := R) (parity bs) = (bs.map (bitSign (R := R))).prod := by
  induction bs with
  | nil => simp [parity, bitSign]
  | cons b bs ih => simp only [parity, sign_xor, List.map_cons, List.prod_cons, ih]

def dotBits {k : ℕ} (a b : Cube k) : Bool :=
  parity (List.ofFn fun i => a i && b i)

theorem character_eq_sign_dot {k : ℕ} (a b : Cube k) :
    character (R := R) a b = bitSign (R := R) (dotBits a b) := by
  rw [dotBits, sign_parity, List.map_ofFn, List.prod_ofFn]
  rfl

theorem character_xor {k : ℕ} (a b c : Cube k) :
    character (R := R) (xorBits a b) c =
      character (R := R) a c * character (R := R) b c := by
  simp only [character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases ha : a i <;> cases hb : b i <;> cases hc : c i <;>
    norm_num [xorBits, bitChar, ha, hb, hc]

theorem character_zero {k : ℕ} (a : Cube k) :
    character (R := R) (zeroBits k) a = 1 := by
  simp [character, zeroBits, bitChar]

def xorFold {k : ℕ} : List (Cube k) → Cube k
  | [] => zeroBits k
  | a :: as => xorBits a (xorFold as)

theorem character_xorFold {k : ℕ} (as : List (Cube k)) (a : Cube k) :
    character (R := R) (xorFold as) a =
      (as.map fun b => character (R := R) b a).prod := by
  induction as with
  | nil => simp [xorFold, character_zero]
  | cons b bs ih => simp only [xorFold, character_xor, List.map_cons, List.prod_cons, ih]

/-- A binary matrix acting by xor of the columns selected by v. -/
def columnMap {n k : ℕ} (columns : Fin n → Cube k) (v : Cube n) : Cube k :=
  xorFold (List.ofFn fun i => if v i then columns i else zeroBits k)

theorem xorBits_zero {k : ℕ} (a : Cube k) : xorBits a (zeroBits k) = a := by
  funext i
  simp [xorBits, zeroBits]

theorem xorFold_replicate_zero (n k : ℕ) :
    xorFold (List.replicate n (zeroBits k)) = zeroBits k := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, xorFold, ih, xorBits_zero]

theorem columnMap_zero {n k : ℕ} (columns : Fin n → Cube k) :
    columnMap columns (zeroBits n) = zeroBits k := by
  simp [columnMap, zeroBits, List.ofFn_const, xorFold_replicate_zero]

/-- The actual transpose matrix character locator in (A5). -/
def transposeMap {n k : ℕ} (columns : Fin n → Cube k) (a : Cube k) : Cube n :=
  fun i => dotBits (columns i) a

theorem transpose_character {n k : ℕ} (columns : Fin n → Cube k)
    (a : Cube k) (v : Cube n) :
    character (R := R) a (columnMap columns v) =
      character (R := R) (transposeMap columns a) v := by
  rw [character_symmetric, columnMap, character_xorFold, List.map_ofFn, List.prod_ofFn]
  change (∏ i, character (R := R) (if v i then columns i else zeroBits k) a) =
    ∏ i, bitChar (R := R) (transposeMap columns a i) (v i)
  apply Finset.prod_congr rfl
  intro i hi
  cases hv : v i
  · simp [character_zero, bitChar]
  · simpa [hv, bitChar, transposeMap, bitSign] using
      character_eq_sign_dot (R := R) (columns i) a

/-- Inversion using the genuine transpose output locator, not an inverse locator. -/
theorem walsh_inversion_transpose {k : ℕ} (columns : Fin k → Cube k)
    (hgood : Function.Bijective (columnMap columns)) (f : Cube k → R) (a : Cube k) :
    (∑ v, character (R := R) (transposeMap columns a) v *
      walsh f (columnMap columns v)) = (2 : R)^k * f a := by
  simp_rw [← transpose_character]
  exact walsh_inversion_reindex (Equiv.ofBijective (columnMap columns) hgood) f a

end Characters

/-! ## Exact support and degree-run elimination -/

inductive NormalLetter
  | x1 | x2 | p1 | p2
  deriving DecidableEq, Fintype

inductive OppositeLetter
  | s | v | w
  deriving DecidableEq, Fintype

def normalIsP (n : NormalLetter) : Prop := n = .p1 ∨ n = .p2

instance normalIsPDecidable (n : NormalLetter) : Decidable (normalIsP n) := by
  unfold normalIsP
  infer_instance

def normalSupport {L : ℕ} (n : Fin L → NormalLetter) : Finset (Fin L) :=
  Finset.univ.filter fun i => normalIsP (n i)

def innerCoefficient {R : Type*} [CommRing R] : NormalLetter → OppositeLetter → R
  | .p1, .s => 2
  | .p2, .w => 1
  | _, _ => 0

theorem inner_support {R : Type*} [CommRing R] (n : NormalLetter) (o : OppositeLetter)
    (h : innerCoefficient (R := R) n o ≠ 0) :
    (n = .p1 ∧ o = .s) ∨ (n = .p2 ∧ o = .w) := by
  cases n <;> cases o <;> simp_all [innerCoefficient]

def normalX (b : Bool) : NormalLetter := if b then .x2 else .x1

def oppositeBit (b : Bool) : OppositeLetter := if b then .v else .s

def normalP (b : Bool) : NormalLetter := if b then .p2 else .p1

def oppositeInner (b : Bool) : OppositeLetter := if b then .w else .s

theorem inner_bit_coefficient {R : Type*} [CommRing R] (b : Bool) :
    innerCoefficient (R := R) (normalP b) (oppositeInner b) = if b then 1 else 2 := by
  cases b <;> rfl

theorem inner_product_coefficient {R : Type*} [CommRing R] {m : ℕ} (a : Cube m) :
    (∏ i, innerCoefficient (R := R) (normalP (a i)) (oppositeInner (a i))) =
      (2 : R)^(m-ones a) := by
  classical
  simp_rw [inner_bit_coefficient]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i : Fin m => a i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold ones
  omega

def ordinaryNormal {R : Type*} [CommRing R]
    (normalBit oppositeBit : Bool) (n : NormalLetter) : R :=
  match normalBit, oppositeBit, n with
  | false, false, .x1 => 1
  | false, false, .p1 => 1
  | false, false, .p2 => 1
  | false, true, .x1 => 1
  | false, true, .p1 => 1
  | true, false, .x2 => 1
  | true, false, .p2 => -1
  | true, true, .x2 => 1
  | _, _, _ => 0

def ordinaryOpposite {R : Type*} [CommRing R]
    (normalBit oppositeBit : Bool) : OppositeLetter → R
  | .s => 1
  | .v => if oppositeBit then -1 else 1
  | .w => if normalBit then (if oppositeBit then 1 else -1) else 0

theorem ordinary_normal_x {R : Type*} [CommRing R] (i j b : Bool) :
    ordinaryNormal (R := R) i j (normalX b) = if b = i then 1 else 0 := by
  cases i <;> cases j <;> cases b <;> norm_num [ordinaryNormal, normalX]

theorem outside_coefficient {R : Type*} [CommRing R] (i j v : Bool) :
    ordinaryNormal (R := R) i j (normalX i) *
      ordinaryOpposite (R := R) i j (oppositeBit v) = bitChar (R := R) j v := by
  cases i <;> cases j <;> cases v <;>
    norm_num [ordinaryNormal, ordinaryOpposite, normalX, oppositeBit, bitChar]

/-- All three actual opposite letters, plus a zero fourth state for the
impossible simultaneous v/w assignment. -/
def outsideProduct {R : Type*} [CommRing R] {k : ℕ}
    (normalBits locator v w : Cube k) : R :=
  ∏ i, if v i && w i then 0 else
    ordinaryOpposite (R := R) (normalBits i) (locator i)
      (if w i then .w else oppositeBit (v i))

theorem outsideProduct_no_w {R : Type*} [CommRing R] {k : ℕ}
    (normalBits locator v : Cube k) :
    outsideProduct (R := R) normalBits locator v (zeroBits k) = character (R := R) locator v := by
  unfold outsideProduct character
  apply Finset.prod_congr rfl
  intro i hi
  cases hn : normalBits i <;> cases hl : locator i <;> cases hv : v i <;>
    norm_num [zeroBits, oppositeBit, ordinaryOpposite, bitChar, hn, hl, hv]

theorem source_support_eq_query {L m : ℕ} (query source : Finset (Fin L))
    (hquery : query.card = m) (hsource : source.card = m)
    (hinner : query ⊆ source) : source = query := by
  exact (Finset.eq_of_subset_of_card_le hinner (by omega)).symm

/-- The local tensor forces the actual normal source support to be the query
support. This uses nonzero products only in the valid one-way direction and
therefore needs no integral-domain or characteristic assumption. -/
theorem raw_normal_support_eq_query {R : Type*} [CommRing R] {L m : ℕ}
    (query : Finset (Fin L)) (normal : Fin L → NormalLetter)
    (opposite : Fin L → OppositeLetter) (hquery : query.card = m)
    (hsource : (normalSupport normal).card = m)
    (hterm : (∏ i ∈ query, innerCoefficient (R := R) (normal i) (opposite i)) ≠ 0) :
    normalSupport normal = query := by
  apply source_support_eq_query query (normalSupport normal) hquery hsource
  intro i hi
  have hc : innerCoefficient (R := R) (normal i) (opposite i) ≠ 0 := by
    intro hz
    exact hterm (Finset.prod_eq_zero hi hz)
  have hp := inner_support (normal i) (opposite i) hc
  simp only [normalSupport, Finset.mem_filter, Finset.mem_univ, true_and, normalIsP]
  exact hp.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- The two runs in (A3)--(A4) agree only if both outside-w sets are empty. -/
theorem equal_degree_runs {k : ℕ} (a b : ℕ) (outsideL outsideR : Cube k) :
    (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) =
        (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ) ↔
      outsideL = zeroBits k ∧ outsideR = zeroBits k := by
  constructor
  · intro h
    have hl : ones outsideL = 0 := by omega
    have hr : ones outsideR = 0 := by omega
    exact ⟨(ones_eq_zero _).mp hl, (ones_eq_zero _).mp hr⟩
  · rintro ⟨rfl, rfl⟩
    have hzero := (ones_eq_zero (zeroBits k)).mpr rfl
    simp [hzero]

theorem equal_run_in_range {m k : ℕ} (a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (outsideL outsideR : Cube k)
    (h : (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) =
      (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ)) :
    (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) ∈
      Finset.Icc (-(m : ℤ)) (m : ℤ) := by
  simp only [Finset.mem_Icc]
  constructor <;> omega

/-- Summing the two actual source run masks over the prescribed 2m+1 runs
is exactly the equality filter. There is no omitted out-of-range equal run. -/
theorem sum_bounded_run_masks {R : Type*} [CommRing R] {m k : ℕ}
    (a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (outsideL outsideR : Cube k) (value : R) :
    (∑ d ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      if ((b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) = d ∧
        (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ) = d) then value else 0) =
      if (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) =
        (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ) then value else 0 := by
  classical
  by_cases h : (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) =
      (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ)
  · have hm := equal_run_in_range a b ha hb outsideL outsideR h
    rw [if_pos h]
    calc
      _ = ∑ d ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
          if (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) = d then value else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [← h, and_self]
      _ = value := Finset.sum_ite_eq_of_mem _ _ (fun _ => value) hm
  · have hn (d : ℤ) : ¬((b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) = d ∧
        (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ) = d) := by omega
    simp [hn, h]

theorem sum_bounded_run_bits {R : Type*} [CommRing R] {m k : ℕ}
    (a b : Cube m) (outsideL outsideR : Cube k) (value : R) :
    (∑ d ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      if ((ones b : ℤ) + (ones outsideR : ℤ) - (ones a : ℤ) = d ∧
        (ones b : ℤ) - (ones a : ℤ) - (ones outsideL : ℤ) = d) then value else 0) =
      if (ones b : ℤ) + (ones outsideR : ℤ) - (ones a : ℤ) =
        (ones b : ℤ) - (ones a : ℤ) - (ones outsideL : ℤ) then value else 0 :=
  sum_bounded_run_masks (ones a) (ones b) (ones_le a) (ones_le b) outsideL outsideR value

/-- All pollution amplitudes may be arbitrary: the actual degree filter kills
them before their values are used. -/
theorem sum_degree_filter {R : Type*} [CommRing R] {k : ℕ}
    (a b : ℕ) (amplitude : Cube k → Cube k → R) :
    (∑ outsideL, ∑ outsideR,
      if (b : ℤ) + (ones outsideR : ℤ) - (a : ℤ) =
          (b : ℤ) - (a : ℤ) - (ones outsideL : ℤ)
      then amplitude outsideL outsideR else 0) =
        amplitude (zeroBits k) (zeroBits k) := by
  classical
  simp_rw [equal_degree_runs]
  simp [ite_and]

/-! ## The full raw A3--A4 sources and interference elimination

The following arrays are defined on every 4-letter normal word and 3-letter
opposite word. Their support test really sets nongood normal slots to zero.
Inputs are indexed by a normal good set and a full Boolean normal coordinate;
the latter has zeros at p positions and is the usual outside row/column index.
This redundant indexing allows every good set to coexist in the same source.
-/

def normalOuterBits {L : ℕ} (normal : Fin L → NormalLetter) : Cube L :=
  fun i => decide (normal i = .x2)

def normalP2Bits {L : ℕ} (normal : Fin L → NormalLetter) : Cube L :=
  fun i => decide (normal i = .p2)

def oppositeVBits {L : ℕ} (opposite : Fin L → OppositeLetter) : Cube L :=
  fun i => decide (opposite i = .v)

def oppositeWBits {L : ℕ} (opposite : Fin L → OppositeLetter) : Cube L :=
  fun i => decide (opposite i = .w)

abbrev RawLeftInput (L m k : ℕ) (R : Type*) :=
  Finset (Fin L) → Cube L → Cube k → Cube m → Cube m → R

abbrev RawRightInput (L m k : ℕ) (R : Type*) :=
  Finset (Fin L) → Cube L → Cube m → Cube m → Cube k → R

def rawLeftSource {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : R :=
  if normalSupport normal ∈ good ∧
      (ones (oppositeWBits opposite) : ℤ) - (ones (normalP2Bits normal) : ℤ) = run
  then (2 : R)^(ones (normalP2Bits normal)) * walsh
    (fun outer => X (normalSupport normal) (normalOuterBits normal) outer
      (gamma (normalP2Bits normal)) (gamma (oppositeWBits opposite)))
    (delta (oppositeVBits opposite)) else 0

def rawRightSource {R : Type*} [CommRing R] {L m k : ℕ}
    (Y : RawRightInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : R :=
  if normalSupport normal ∈ good ∧
      (ones (normalP2Bits normal) : ℤ) - (ones (oppositeWBits opposite) : ℤ) = run
  then (2 : R)^(ones (normalP2Bits normal)) * walsh
    (fun outer => Y (normalSupport normal) (normalOuterBits normal)
      (gamma (oppositeWBits opposite)) (gamma (normalP2Bits normal)) outer)
    (delta (oppositeVBits opposite)) else 0

theorem raw_left_nongood {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (hbad : normalSupport normal ∉ good) :
    rawLeftSource X good gamma delta run normal opposite = 0 := by
  simp [rawLeftSource, hbad]

theorem raw_right_nongood {R : Type*} [CommRing R] {L m k : ℕ}
    (Y : RawRightInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (hbad : normalSupport normal ∉ good) :
    rawRightSource Y good gamma delta run normal opposite = 0 := by
  simp [rawRightSource, hbad]

/-- Any other good source slot is killed by the actual queried inner tensor.
The opposite word in the inner kernel belongs to the other input, whereas
the opposite word in the source belongs to this input's second half. -/
theorem raw_left_wrong_slot {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (query : Finset (Fin L)) (normal : Fin L → NormalLetter)
    (queryOpposite sourceOpposite : Fin L → OppositeLetter)
    (hquery : query.card = m) (hgood : ∀ S ∈ good, S.card = m)
    (hwrong : normalSupport normal ≠ query) :
    (∏ i ∈ query, innerCoefficient (R := R) (normal i) (queryOpposite i)) *
      rawLeftSource X good gamma delta run normal sourceOpposite = 0 := by
  by_cases hs : normalSupport normal ∈ good
  · have hz : (∏ i ∈ query, innerCoefficient (R := R) (normal i) (queryOpposite i)) = 0 := by
      by_contra hn
      exact hwrong (raw_normal_support_eq_query query normal queryOpposite hquery (hgood _ hs) hn)
    rw [hz, zero_mul]
  · rw [raw_left_nongood X good gamma delta run normal sourceOpposite hs, mul_zero]

theorem raw_right_wrong_slot {R : Type*} [CommRing R] {L m k : ℕ}
    (Y : RawRightInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (query : Finset (Fin L)) (normal : Fin L → NormalLetter)
    (queryOpposite sourceOpposite : Fin L → OppositeLetter)
    (hquery : query.card = m) (hgood : ∀ S ∈ good, S.card = m)
    (hwrong : normalSupport normal ≠ query) :
    (∏ i ∈ query, innerCoefficient (R := R) (normal i) (queryOpposite i)) *
      rawRightSource Y good gamma delta run normal sourceOpposite = 0 := by
  by_cases hs : normalSupport normal ∈ good
  · have hz : (∏ i ∈ query, innerCoefficient (R := R) (normal i) (queryOpposite i)) = 0 := by
      by_contra hn
      exact hwrong (raw_normal_support_eq_query query normal queryOpposite hquery (hgood _ hs) hn)
    rw [hz, zero_mul]
  · rw [raw_right_nongood Y good gamma delta run normal sourceOpposite hs, mul_zero]

def rawHalfKernel {R : Type*} [CommRing R] {L : ℕ} (query : Finset (Fin L))
    (normalBits locator : Cube L) (normal : Fin L → NormalLetter)
    (opposite : Fin L → OppositeLetter) : R :=
  (∏ i ∈ query, innerCoefficient (R := R) (normal i) (opposite i)) *
    ∏ i ∈ queryᶜ, ordinaryNormal (R := R) (normalBits i) (locator i) (normal i) *
      ordinaryOpposite (R := R) (normalBits i) (locator i) (opposite i)

/-- The actual two-half raw tensor summand, before any word restriction. -/
def rawPairTerm {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (queryL queryR : Finset (Fin L)) (normalL normalR locatorL locatorR : Cube L)
    (run : ℤ) (nL nR : Fin L → NormalLetter) (oL oR : Fin L → OppositeLetter) : R :=
  rawHalfKernel queryL normalL locatorL nL oL * rawHalfKernel queryR normalR locatorR nR oR *
    rawLeftSource X good gamma delta run nL oR * rawRightSource Y good gamma delta run nR oL

noncomputable def rawContraction {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (queryL queryR : Finset (Fin L)) (normalL normalR locatorL locatorR : Cube L) : R :=
  ∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), ∑ nL, ∑ nR, ∑ oL, ∑ oR,
    rawPairTerm X Y good gamma delta queryL queryR normalL normalR locatorL locatorR run nL nR oL oR

abbrev Subsets {L : ℕ} (Q : Finset (Fin L)) := {T : Finset (Fin L) // T ⊆ Q}

def setBits {L : ℕ} (T : Finset (Fin L)) : Cube L := fun i => decide (i ∈ T)

def outsideBits {L : ℕ} (Q : Finset (Fin L)) (i : Cube L) : Cube L :=
  fun j => if j ∈ Q then false else i j

def canonicalNormal {L : ℕ} (Q : Finset (Fin L)) (i : Cube L) (T : Subsets Q)
    (j : Fin L) : NormalLetter :=
  if j ∈ Q then (if j ∈ T.val then .p2 else .p1) else normalX (i j)

def canonicalOpposite {L : ℕ} (Q : Finset (Fin L))
    (T : Subsets Q) (V : Subsets Qᶜ) (j : Fin L) : OppositeLetter :=
  if j ∈ Q then (if j ∈ T.val then .w else .s) else oppositeBit (decide (j ∈ V.val))

theorem ones_setBits {L : ℕ} (T : Finset (Fin L)) : ones (setBits T) = T.card := by
  simp [ones, setBits]

theorem canonicalNormal_support {L : ℕ} (Q : Finset (Fin L)) (i : Cube L) (T : Subsets Q) :
    normalSupport (canonicalNormal Q i T) = Q := by
  ext j
  by_cases hq : j ∈ Q
  · by_cases ht : j ∈ T.val <;> simp [normalSupport, canonicalNormal, normalIsP, hq, ht]
  · cases hi : i j <;> simp [normalSupport, canonicalNormal, normalIsP, normalX, hq, hi]

theorem canonicalNormal_p2 {L : ℕ} (Q : Finset (Fin L)) (i : Cube L) (T : Subsets Q) :
    normalP2Bits (canonicalNormal Q i T) = setBits T.val := by
  funext j
  have hT : j ∈ T.val → j ∈ Q := fun h => T.property h
  by_cases hq : j ∈ Q <;> by_cases ht : j ∈ T.val <;> cases hi : i j <;>
    simp_all [normalP2Bits, canonicalNormal, normalX, setBits]

theorem canonicalNormal_outer {L : ℕ} (Q : Finset (Fin L)) (i : Cube L) (T : Subsets Q) :
    normalOuterBits (canonicalNormal Q i T) = outsideBits Q i := by
  funext j
  by_cases hq : j ∈ Q <;> by_cases ht : j ∈ T.val <;> cases hi : i j <;>
    simp [normalOuterBits, canonicalNormal, normalX, outsideBits, hq, ht, hi]

theorem canonicalOpposite_w {L : ℕ} (Q : Finset (Fin L)) (T : Subsets Q) (V : Subsets Qᶜ) :
    oppositeWBits (canonicalOpposite Q T V) = setBits T.val := by
  funext j
  have hT : j ∈ T.val → j ∈ Q := fun h => T.property h
  by_cases hq : j ∈ Q <;> by_cases ht : j ∈ T.val <;> by_cases hv : j ∈ V.val <;>
    simp_all [oppositeWBits, canonicalOpposite, oppositeBit, setBits]

theorem canonicalOpposite_v {L : ℕ} (Q : Finset (Fin L)) (T : Subsets Q) (V : Subsets Qᶜ) :
    oppositeVBits (canonicalOpposite Q T V) = setBits V.val := by
  funext j
  have hV : j ∈ V.val → j ∉ Q := fun h => Finset.mem_compl.mp (V.property h)
  by_cases hq : j ∈ Q <;> by_cases ht : j ∈ T.val <;> by_cases hv : j ∈ V.val <;>
    simp_all [oppositeVBits, canonicalOpposite, oppositeBit, setBits]

theorem raw_half_canonical {R : Type*} [CommRing R] {L : ℕ}
    (Q : Finset (Fin L)) (i j : Cube L) (T : Subsets Q) (V : Subsets Qᶜ) :
    rawHalfKernel (R := R) Q i j (canonicalNormal Q i T) (canonicalOpposite Q T V) =
      (2 : R)^(Q.card-T.val.card) * character j (setBits V.val) := by
  classical
  have hinner : (∏ x ∈ Q, innerCoefficient (R := R)
      (canonicalNormal Q i T x) (canonicalOpposite Q T V x)) =
        (2 : R)^(Q.card-T.val.card) := by
    calc
      _ = ∏ x ∈ Q, if x ∈ T.val then (1 : R) else 2 := by
        apply Finset.prod_congr rfl
        intro x hx
        by_cases ht : x ∈ T.val <;> simp [canonicalNormal, canonicalOpposite, innerCoefficient, hx, ht]
      _ = _ := by
        rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
        congr 1
        have heq : Q.filter (fun x => x ∈ T.val) = T.val := by
          ext x
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨T.property h, h⟩⟩
        have hc := Finset.card_filter_add_card_filter_not (s := Q) (p := fun x => x ∈ T.val)
        rw [heq] at hc
        omega
  have hout : (∏ x ∈ Qᶜ, ordinaryNormal (R := R) (i x) (j x) (canonicalNormal Q i T x) *
      ordinaryOpposite (R := R) (i x) (j x) (canonicalOpposite Q T V x)) =
        character j (setBits V.val) := by
    calc
      _ = ∏ x ∈ Qᶜ, bitChar (R := R) (j x) (setBits V.val x) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hn : x ∉ Q := Finset.mem_compl.mp hx
        simpa only [canonicalNormal, canonicalOpposite, if_neg hn, setBits] using
          outside_coefficient (R := R) (i x) (j x) (decide (x ∈ V.val))
      _ = _ := by
        apply Finset.prod_subset (Finset.subset_univ Qᶜ)
        intro x hx hn
        have hq : x ∈ Q := by simpa using hn
        have hv : x ∉ V.val := by
          intro hv
          exact (Finset.mem_compl.mp (V.property hv)) hq
        simp [bitChar, setBits, hv]
  exact congrArg₂ (fun a b : R => a*b) hinner hout

theorem raw_left_canonical {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (iL : Cube L) (tL : Subsets QL) (tR : Subsets QR)
    (vR : Subsets QRᶜ) (run : ℤ) (hgood : QL ∈ good) :
    rawLeftSource X good gamma delta run (canonicalNormal QL iL tL) (canonicalOpposite QR tR vR) =
      if (tR.val.card : ℤ) - (tL.val.card : ℤ) = run then
        (2 : R)^tL.val.card * walsh
          (fun outer => X QL (outsideBits QL iL) outer (gamma (setBits tL.val)) (gamma (setBits tR.val)))
          (delta (setBits vR.val)) else 0 := by
  simp only [rawLeftSource, canonicalNormal_support, hgood, true_and,
    canonicalNormal_p2, canonicalNormal_outer, canonicalOpposite_w, canonicalOpposite_v, ones_setBits]

theorem raw_right_canonical {R : Type*} [CommRing R] {L m k : ℕ}
    (Y : RawRightInput L m k R) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (iR : Cube L) (tL : Subsets QL) (tR : Subsets QR)
    (vL : Subsets QLᶜ) (run : ℤ) (hgood : QR ∈ good) :
    rawRightSource Y good gamma delta run (canonicalNormal QR iR tR) (canonicalOpposite QL tL vL) =
      if (tR.val.card : ℤ) - (tL.val.card : ℤ) = run then
        (2 : R)^tR.val.card * walsh
          (fun outer => Y QR (outsideBits QR iR) (gamma (setBits tL.val)) (gamma (setBits tR.val)) outer)
          (delta (setBits vL.val)) else 0 := by
  simp only [rawRightSource, canonicalNormal_support, hgood, true_and,
    canonicalNormal_p2, canonicalNormal_outer, canonicalOpposite_w, canonicalOpposite_v, ones_setBits]

theorem raw_pair_canonical_run_sum {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (QL QR : Finset (Fin L)) (iL iR jL jR : Cube L)
    (hQL : QL.card = m) (hQR : QR.card = m) (hgL : QL ∈ good) (hgR : QR ∈ good)
    (tL : Subsets QL) (tR : Subsets QR) (vL : Subsets QLᶜ) (vR : Subsets QRᶜ) :
    (∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      rawPairTerm X Y good gamma delta QL QR iL iR jL jR run
        (canonicalNormal QL iL tL) (canonicalNormal QR iR tR)
        (canonicalOpposite QL tL vL) (canonicalOpposite QR tR vR)) =
      ((2 : R)^(m-tL.val.card) * character jL (setBits vL.val)) *
      ((2 : R)^(m-tR.val.card) * character jR (setBits vR.val)) *
      ((2 : R)^tL.val.card * walsh
        (fun outer => X QL (outsideBits QL iL) outer (gamma (setBits tL.val)) (gamma (setBits tR.val)))
        (delta (setBits vR.val))) *
      ((2 : R)^tR.val.card * walsh
        (fun outer => Y QR (outsideBits QR iR) (gamma (setBits tL.val)) (gamma (setBits tR.val)) outer)
        (delta (setBits vL.val))) := by
  classical
  have htL : tL.val.card ≤ m := by simpa only [hQL] using Finset.card_le_card tL.property
  have htR : tR.val.card ≤ m := by simpa only [hQR] using Finset.card_le_card tR.property
  have hr : (tR.val.card : ℤ) - (tL.val.card : ℤ) ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  simp only [rawPairTerm, raw_half_canonical, hQL, hQR]
  simp_rw [raw_left_canonical X good gamma delta QL QR iL tL tR vR _ hgL,
    raw_right_canonical Y good gamma delta QL QR iR tL tR vL _ hgR]
  simp_rw [mul_ite, ite_mul, mul_zero, zero_mul, ite_self]
  simp only [Finset.sum_ite_eq, if_pos hr, ite_true]

/-- The surviving raw summands, indexed by the four genuine supported sets.
The summand is still rawPairTerm, so this definition cannot assume A6. -/
noncomputable def survivingContraction {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m) (delta : Cube L → Cube k)
    (queryL queryR : Finset (Fin L)) (normalL normalR locatorL locatorR : Cube L) : R :=
  ∑ tL : Subsets queryL, ∑ tR : Subsets queryR,
    ∑ vL : Subsets queryLᶜ, ∑ vR : Subsets queryRᶜ,
    ∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      rawPairTerm X Y good gamma delta queryL queryR normalL normalR locatorL locatorR run
        (canonicalNormal queryL normalL tL) (canonicalNormal queryR normalR tR)
        (canonicalOpposite queryL tL vL) (canonicalOpposite queryR tR vR)

/-- The original good restricted Gamma/Delta maps. Agreement is pointwise on
supported sets; no output-value or contraction identity is assumed. -/
structure RestrictedGoodMaps {L m k : ℕ} (QL QR : Finset (Fin L))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) where
  gammaL : Subsets QL ≃ Cube m
  gammaR : Subsets QR ≃ Cube m
  deltaL : Subsets QLᶜ ≃ Cube k
  deltaR : Subsets QRᶜ ≃ Cube k
  gammaL_spec : ∀ t, gamma (setBits t.val) = gammaL t
  gammaR_spec : ∀ t, gamma (setBits t.val) = gammaR t
  deltaL_spec : ∀ v, delta (setBits v.val) = deltaL v
  deltaR_spec : ∀ v, delta (setBits v.val) = deltaR v

theorem walsh_pair_reindex {R : Type*} [CommRing R] {k : ℕ}
    {VL VR : Type*} [Fintype VL] [Fintype VR]
    (deltaL : VL ≃ Cube k) (deltaR : VR ≃ Cube k)
    (f g : Cube k → R) (aL aR : Cube k) :
    (∑ vL, ∑ vR,
      (character (R := R) aL (deltaR vR) * walsh f (deltaR vR)) *
      (character (R := R) aR (deltaL vL) * walsh g (deltaL vL))) =
      ((2 : R)^k*f aL) * ((2 : R)^k*g aR) := by
  classical
  calc
    _ = (∑ vR, character (R := R) aL (deltaR vR) * walsh f (deltaR vR)) *
        (∑ vL, character (R := R) aR (deltaL vL) * walsh g (deltaL vL)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [walsh_inversion_reindex deltaR, walsh_inversion_reindex deltaL]

theorem source_weight_counts {R : Type*} [CommRing R] (m a b : ℕ)
    (ha : a ≤ m) (hb : b ≤ m) :
    (2 : R)^(m-a) * (2 : R)^(m-b) * (2 : R)^a * (2 : R)^b = (2 : R)^(2*m) := by
  have h1 := Nat.sub_add_cancel ha
  have h2 := Nat.sub_add_cancel hb
  calc
    _ = ((2 : R)^(m-a)*(2 : R)^a) * ((2 : R)^(m-b)*(2 : R)^b) := by ring
    _ = (2 : R)^m*(2 : R)^m := by rw [← pow_add, ← pow_add, h1, h2]
    _ = (2 : R)^(2*m) := by rw [← pow_add]; congr 1; omega

/-- A6 for the surviving summands of the actual raw arrays, using genuine
transpose characters and the good restricted maps. -/
theorem surviving_contraction_eq_scaled_product {R : Type*} [CommRing R] {L m k : ℕ}
    (X : RawLeftInput L m k R) (Y : RawRightInput L m k R)
    (good : Finset (Finset (Fin L))) (gamma : Cube L → Cube m)
    (columns : Fin L → Cube k) (QL QR : Finset (Fin L))
    (iL iR : Cube L) (aL aR : Cube k)
    (hQL : QL.card = m) (hQR : QR.card = m) (hgL : QL ∈ good) (hgR : QR ∈ good)
    (maps : RestrictedGoodMaps QL QR gamma (columnMap columns)) :
    survivingContraction X Y good gamma (columnMap columns) QL QR iL iR
        (transposeMap columns aR) (transposeMap columns aL) =
      (4 : R)^(m+k) * ∑ h1, ∑ h2,
        X QL (outsideBits QL iL) aL h1 h2 * Y QR (outsideBits QR iR) h1 h2 aR := by
  classical
  let FX (tL : Subsets QL) (tR : Subsets QR) : Cube k → R :=
    fun outer => X QL (outsideBits QL iL) outer (maps.gammaL tL) (maps.gammaR tR)
  let FY (tL : Subsets QL) (tR : Subsets QR) : Cube k → R :=
    fun outer => Y QR (outsideBits QR iR) (maps.gammaL tL) (maps.gammaR tR) outer
  have hp : (2 : R)^(2*m) * (2 : R)^k * (2 : R)^k = (4 : R)^(m+k) := by
    calc
      _ = (2 : R)^(2*(m+k)) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ = (4 : R)^(m+k) := by rw [pow_mul]; norm_num
  have hpair (tL : Subsets QL) (tR : Subsets QR) (vL : Subsets QLᶜ) (vR : Subsets QRᶜ) :
      (∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        rawPairTerm X Y good gamma (columnMap columns) QL QR iL iR
          (transposeMap columns aR) (transposeMap columns aL) run
          (canonicalNormal QL iL tL) (canonicalNormal QR iR tR)
          (canonicalOpposite QL tL vL) (canonicalOpposite QR tR vR)) =
        (2 : R)^(2*m) *
          ((character (R := R) aL (maps.deltaR vR) * walsh (FX tL tR) (maps.deltaR vR)) *
           (character (R := R) aR (maps.deltaL vL) * walsh (FY tL tR) (maps.deltaL vL))) := by
    rw [raw_pair_canonical_run_sum X Y good gamma (columnMap columns) QL QR iL iR
      (transposeMap columns aR) (transposeMap columns aL) hQL hQR hgL hgR]
    simp_rw [← transpose_character, maps.gammaL_spec, maps.gammaR_spec,
      maps.deltaL_spec, maps.deltaR_spec]
    have htL : tL.val.card ≤ m := by simpa only [hQL] using Finset.card_le_card tL.property
    have htR : tR.val.card ≤ m := by simpa only [hQR] using Finset.card_le_card tR.property
    have hw := source_weight_counts (R := R) m tL.val.card tR.val.card htL htR
    dsimp [FX, FY]
    calc
      _ = ((2 : R)^(m-tL.val.card) * (2 : R)^(m-tR.val.card) *
          (2 : R)^tL.val.card * (2 : R)^tR.val.card) *
          ((character aL (maps.deltaR vR) * walsh
              (fun outer => X QL (outsideBits QL iL) outer (maps.gammaL tL) (maps.gammaR tR))
              (maps.deltaR vR)) *
           (character aR (maps.deltaL vL) * walsh
              (fun outer => Y QR (outsideBits QR iR) (maps.gammaL tL) (maps.gammaR tR) outer)
              (maps.deltaL vL))) := by ring
      _ = _ := by rw [hw]
  have hinner (tL : Subsets QL) (tR : Subsets QR) :
      (∑ vL : Subsets QLᶜ, ∑ vR : Subsets QRᶜ,
        ∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
          rawPairTerm X Y good gamma (columnMap columns) QL QR iL iR
            (transposeMap columns aR) (transposeMap columns aL) run
            (canonicalNormal QL iL tL) (canonicalNormal QR iR tR)
            (canonicalOpposite QL tL vL) (canonicalOpposite QR tR vR)) =
        (4 : R)^(m+k) * (FX tL tR aL * FY tL tR aR) := by
    simp_rw [hpair, ← Finset.mul_sum]
    rw [walsh_pair_reindex maps.deltaL maps.deltaR]
    calc
      _ = ((2 : R)^(2*m)*(2 : R)^k*(2 : R)^k) * (FX tL tR aL * FY tL tR aR) := by ring
      _ = _ := by rw [hp]
  unfold survivingContraction
  simp_rw [hinner, ← Finset.mul_sum]
  congr 1
  dsimp [FX, FY]
  calc
    _ = ∑ tL : Subsets QL, ∑ h2 : Cube m,
        X QL (outsideBits QL iL) aL (maps.gammaL tL) h2 *
          Y QR (outsideBits QR iR) (maps.gammaL tL) h2 aR := by
      apply Finset.sum_congr rfl
      intro tL htL
      exact maps.gammaR.sum_comp (fun h2 => X QL (outsideBits QL iL) aL (maps.gammaL tL) h2 *
        Y QR (outsideBits QR iR) (maps.gammaL tL) h2 aR)
    _ = _ := maps.gammaL.sum_comp (fun h1 => ∑ h2,
      X QL (outsideBits QL iL) aL h1 h2 * Y QR (outsideBits QR iR) h1 h2 aR)

section Sources

variable {R : Type*} [CommRing R]

/-- The p1-s coefficients together with the normal p2 source weights. -/
theorem inner_source_normalization {m : ℕ} (a b : Cube m) :
    (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
        (2 : R)^(ones a) * (2 : R)^(ones b) = (2 : R)^(2*m) := by
  have ha : m - ones a + ones a = m := Nat.sub_add_cancel (ones_le a)
  have hb : m - ones b + ones b = m := Nat.sub_add_cancel (ones_le b)
  calc
    _ = ((2 : R)^(m-ones a) * (2 : R)^(ones a)) *
        ((2 : R)^(m-ones b) * (2 : R)^(ones b)) := by ring
    _ = (2 : R)^m * (2 : R)^m := by rw [← pow_add, ← pow_add, ha, hb]
    _ = (2 : R)^(2*m) := by rw [← pow_add]; congr 1; omega

/-- A3 on the matched normal support, retaining its genuine normal weight. -/
def leftSource {m k : ℕ} (X : Cube k → Cube m → Cube m → R)
    (gammaL gammaR : Cube m ≃ Cube m) (deltaR : Cube k ≃ Cube k)
    (a b : Cube m) (vR : Cube k) : R :=
  (2 : R)^(ones a) *
    walsh (fun outer => X outer (gammaL a) (gammaR b)) (deltaR vR)

/-- A4 on the matched normal support, with the opposite outer index transformed. -/
def rightSource {m k : ℕ} (Y : Cube m → Cube m → Cube k → R)
    (gammaL gammaR : Cube m ≃ Cube m) (deltaL : Cube k ≃ Cube k)
    (a b : Cube m) (vL : Cube k) : R :=
  (2 : R)^(ones b) *
    walsh (fun outer => Y (gammaL a) (gammaR b) outer) (deltaL vL)

/-- The source contraction after normal-support localization and degree filtering.
The character at delta(v) is the transpose-Delta output character (A5). -/
def matchedContraction {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R)
    (gammaL gammaR : Cube m ≃ Cube m)
    (deltaL deltaR : Cube k ≃ Cube k) (outerL outerR : Cube k) : R :=
  ∑ a, ∑ b, ∑ vL, ∑ vR,
    (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
      character (R := R) outerL (deltaR vR) *
      character (R := R) outerR (deltaL vL) *
      leftSource X gammaL gammaR deltaR a b vR *
      rightSource Y gammaL gammaR deltaL a b vL

theorem matched_term_sum {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R)
    (gammaL gammaR : Cube m ≃ Cube m)
    (deltaL deltaR : Cube k ≃ Cube k) (outerL outerR : Cube k)
    (a b : Cube m) :
    (∑ vL, ∑ vR,
      (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
        character (R := R) outerL (deltaR vR) *
        character (R := R) outerR (deltaL vL) *
        leftSource X gammaL gammaR deltaR a b vR *
        rightSource Y gammaL gammaR deltaL a b vL) =
      (2 : R)^(2*m) * ((2 : R)^k * X outerL (gammaL a) (gammaR b)) *
        ((2 : R)^k * Y (gammaL a) (gammaR b) outerR) := by
  classical
  have hterm (vL vR : Cube k) :
      (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
        character (R := R) outerL (deltaR vR) *
        character (R := R) outerR (deltaL vL) *
        leftSource X gammaL gammaR deltaR a b vR *
        rightSource Y gammaL gammaR deltaL a b vL =
      (2 : R)^(2*m) *
        (character (R := R) outerL (deltaR vR) *
          walsh (fun outer => X outer (gammaL a) (gammaR b)) (deltaR vR)) *
        (character (R := R) outerR (deltaL vL) *
          walsh (fun outer => Y (gammaL a) (gammaR b) outer) (deltaL vL)) := by
    unfold leftSource rightSource
    have hn := inner_source_normalization (R := R) a b
    calc
      _ = ((2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
          (2 : R)^(ones a) * (2 : R)^(ones b)) *
        (character (R := R) outerL (deltaR vR) *
          walsh (fun outer => X outer (gammaL a) (gammaR b)) (deltaR vR)) *
        (character (R := R) outerR (deltaL vL) *
          walsh (fun outer => Y (gammaL a) (gammaR b) outer) (deltaL vL)) := by ring
      _ = _ := by rw [hn]
  simp_rw [hterm]
  calc
    _ = (2 : R)^(2*m) *
        (∑ vR, character (R := R) outerL (deltaR vR) *
          walsh (fun outer => X outer (gammaL a) (gammaR b)) (deltaR vR)) *
        (∑ vL, character (R := R) outerR (deltaL vL) *
          walsh (fun outer => Y (gammaL a) (gammaR b) outer) (deltaL vL)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [walsh_inversion_reindex deltaR, walsh_inversion_reindex deltaL]

/-- The scaled product (A6), for the explicitly constructed weighted sources.
No normalization division is used; integer decoding is a separate obligation. -/
theorem matched_contraction_eq_scaled_product {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R)
    (gammaL gammaR : Cube m ≃ Cube m)
    (deltaL deltaR : Cube k ≃ Cube k) (outerL outerR : Cube k) :
    matchedContraction X Y gammaL gammaR deltaL deltaR outerL outerR =
      (4 : R)^(m+k) * ∑ hL, ∑ hR, X outerL hL hR * Y hL hR outerR := by
  classical
  unfold matchedContraction
  simp_rw [matched_term_sum]
  have hp : (2 : R)^(2*m) * (2 : R)^k * (2 : R)^k = (4 : R)^(m+k) := by
    calc
      _ = (2 : R)^(2*(m+k)) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ = (4 : R)^(m+k) := by rw [pow_mul]; norm_num
  have hf (a b : Cube m) :
      (2 : R)^(2*m) * ((2 : R)^k * X outerL (gammaL a) (gammaR b)) *
        ((2 : R)^k * Y (gammaL a) (gammaR b) outerR) =
      (4 : R)^(m+k) * (X outerL (gammaL a) (gammaR b) *
        Y (gammaL a) (gammaR b) outerR) := by
    calc
      _ = ((2 : R)^(2*m) * (2 : R)^k * (2 : R)^k) *
        (X outerL (gammaL a) (gammaR b) * Y (gammaL a) (gammaR b) outerR) := by ring
      _ = _ := by rw [hp]
  simp_rw [hf, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ a, ∑ hR, X outerL (gammaL a) hR * Y (gammaL a) hR outerR := by
      apply Finset.sum_congr rfl
      intro a ha
      exact gammaR.sum_comp (fun hR => X outerL (gammaL a) hR * Y (gammaL a) hR outerR)
    _ = _ := gammaL.sum_comp (fun hL => ∑ hR, X outerL hL hR * Y hL hR outerR)

end Sources

/-! ## Complete outside-w filtering on the source normal form

The layout supplies the actual restricted binary maps: the Gamma restrictions
are bijections, each Delta restriction is a column-xor map with a bijectivity
proof, and the remaining Gamma columns are retained in the raw sources. No
assumption about the value of the output contraction is made.
-/

structure GoodLayout (m k : ℕ) where
  gammaL : Cube m ≃ Cube m
  gammaR : Cube m ≃ Cube m
  deltaColumnsL : Fin k → Cube k
  deltaColumnsR : Fin k → Cube k
  deltaGoodL : Function.Bijective (columnMap deltaColumnsL)
  deltaGoodR : Function.Bijective (columnMap deltaColumnsR)
  gammaOutsideL : Fin k → Cube m
  gammaOutsideR : Fin k → Cube m
  normalL : Cube k
  normalR : Cube k
  outerL : Cube k
  outerR : Cube k

noncomputable def GoodLayout.deltaL {m k : ℕ} (layout : GoodLayout m k) : Cube k ≃ Cube k :=
  Equiv.ofBijective (columnMap layout.deltaColumnsL) layout.deltaGoodL

noncomputable def GoodLayout.deltaR {m k : ℕ} (layout : GoodLayout m k) : Cube k ≃ Cube k :=
  Equiv.ofBijective (columnMap layout.deltaColumnsR) layout.deltaGoodR

def fullGamma {m k : ℕ} (gamma : Cube m ≃ Cube m) (outside : Fin k → Cube m)
    (inner : Cube m) (extra : Cube k) : Cube m :=
  xorBits (gamma inner) (columnMap outside extra)

theorem fullGamma_zero {m k : ℕ} (gamma : Cube m ≃ Cube m) (outside : Fin k → Cube m)
    (inner : Cube m) : fullGamma gamma outside inner (zeroBits k) = gamma inner := by
  simp only [fullGamma, columnMap_zero, xorBits_zero]

section CompleteNormalForm

variable {R : Type*} [CommRing R]

/-- The A3 source retains the outside-w Gamma contribution until the degree
filter removes it. -/
def fullLeftSource {m k : ℕ} (X : Cube k → Cube m → Cube m → R)
    (layout : GoodLayout m k) (a b : Cube m) (outsideR vR : Cube k) : R :=
  (2 : R)^(ones a) * walsh
    (fun outer => X outer (layout.gammaL a)
      (fullGamma layout.gammaR layout.gammaOutsideR b outsideR))
    (columnMap layout.deltaColumnsR vR)

/-- The symmetric A4 source with its normal p2 weight. -/
def fullRightSource {m k : ℕ} (Y : Cube m → Cube m → Cube k → R)
    (layout : GoodLayout m k) (a b : Cube m) (outsideL vL : Cube k) : R :=
  (2 : R)^(ones b) * walsh
    (fun outer => Y (fullGamma layout.gammaL layout.gammaOutsideL a outsideL)
      (layout.gammaR b) outer)
    (columnMap layout.deltaColumnsL vL)

def sourceNormalFormTerm {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k)
    (a b : Cube m) (vL vR outsideL outsideR : Cube k) : R :=
  (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
    outsideProduct layout.normalL (transposeMap layout.deltaColumnsL layout.outerR) vL outsideL *
    outsideProduct layout.normalR (transposeMap layout.deltaColumnsR layout.outerL) vR outsideR *
    fullLeftSource X layout a b outsideR vR *
    fullRightSource Y layout a b outsideL vL

/-- Both raw outside-w populations and all opposite letters are included.
The run test is exactly the equality from A3--A4, not a Boolean surrogate. -/
def sourceContractionNormalForm {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) : R :=
  ∑ a, ∑ b, ∑ vL, ∑ vR, ∑ outsideL, ∑ outsideR,
    if (ones b : ℤ) + (ones outsideR : ℤ) - (ones a : ℤ) =
        (ones b : ℤ) - (ones a : ℤ) - (ones outsideL : ℤ)
    then sourceNormalFormTerm X Y layout a b vL vR outsideL outsideR else 0

/-- The complete normal form with the explicit finite run sum of A3--A4. -/
noncomputable def sourceContractionWithRuns {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) : R :=
  ∑ a, ∑ b, ∑ vL, ∑ vR, ∑ outsideL, ∑ outsideR,
    ∑ d ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      if ((ones b : ℤ) + (ones outsideR : ℤ) - (ones a : ℤ) = d ∧
          (ones b : ℤ) - (ones a : ℤ) - (ones outsideL : ℤ) = d)
      then sourceNormalFormTerm X Y layout a b vL vR outsideL outsideR else 0

theorem bounded_runs_eq_normal_form {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) :
    sourceContractionWithRuns X Y layout = sourceContractionNormalForm X Y layout := by
  classical
  unfold sourceContractionWithRuns sourceContractionNormalForm
  simp_rw [sum_bounded_run_bits]

theorem normal_form_eq_matched {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) :
    sourceContractionNormalForm X Y layout =
      matchedContraction X Y layout.gammaL layout.gammaR layout.deltaL layout.deltaR
        layout.outerL layout.outerR := by
  classical
  unfold sourceContractionNormalForm
  simp_rw [sum_degree_filter]
  unfold sourceNormalFormTerm fullLeftSource fullRightSource
  simp_rw [fullGamma_zero, outsideProduct_no_w, ← transpose_character]
  unfold matchedContraction leftSource rightSource
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro vL hvL
  apply Finset.sum_congr rfl
  intro vR hvR
  change _ = (2 : R)^(m-ones a) * (2 : R)^(m-ones b) *
    character layout.outerL (columnMap layout.deltaColumnsR vR) *
    character layout.outerR (columnMap layout.deltaColumnsL vL) *
    ((2 : R)^(ones a) * walsh
      (fun outer => X outer (layout.gammaL a) (layout.gammaR b))
      (columnMap layout.deltaColumnsR vR)) *
    ((2 : R)^(ones b) * walsh
      (fun outer => Y (layout.gammaL a) (layout.gammaR b) outer)
      (columnMap layout.deltaColumnsL vL))
  ring

/-- The complete source normal form has exactly the A6 normalization, including
the outside-w terms that are eliminated by equal degree runs. -/
theorem source_normal_form_eq_scaled_product {m k : ℕ}
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) :
    sourceContractionNormalForm X Y layout =
      (4 : R)^(m+k) * ∑ hL, ∑ hR, X layout.outerL hL hR * Y hL hR layout.outerR := by
  rw [normal_form_eq_matched]
  exact matched_contraction_eq_scaled_product X Y layout.gammaL layout.gammaR
    layout.deltaL layout.deltaR layout.outerL layout.outerR

theorem source_normal_form_eq_scaled_product_L {L m k : ℕ} (hL : m+k=L)
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) :
    sourceContractionNormalForm X Y layout =
      (4 : R)^L * ∑ h1, ∑ h2, X layout.outerL h1 h2 * Y h1 h2 layout.outerR := by
  simpa only [hL] using source_normal_form_eq_scaled_product X Y layout

theorem source_with_runs_eq_scaled_product {L m k : ℕ} (hL : m+k=L)
    (X : Cube k → Cube m → Cube m → R)
    (Y : Cube m → Cube m → Cube k → R) (layout : GoodLayout m k) :
    sourceContractionWithRuns X Y layout =
      (4 : R)^L * ∑ h1, ∑ h2, X layout.outerL h1 h2 * Y h1 h2 layout.outerR := by
  rw [bounded_runs_eq_normal_form]
  exact source_normal_form_eq_scaled_product_L hL X Y layout

end CompleteNormalForm

#print axioms character_orthogonality
#print axioms walsh_inversion
#print axioms transpose_character
#print axioms raw_normal_support_eq_query
#print axioms raw_left_wrong_slot
#print axioms raw_right_wrong_slot
#print axioms equal_degree_runs
#print axioms sum_degree_filter
#print axioms sum_bounded_run_masks
#print axioms inner_source_normalization
#print axioms matched_contraction_eq_scaled_product
#print axioms source_normal_form_eq_scaled_product
#print axioms source_with_runs_eq_scaled_product
#print axioms raw_pair_canonical_run_sum
#print axioms surviving_contraction_eq_scaled_product

end ThinMatrix.WalshEmbedding
