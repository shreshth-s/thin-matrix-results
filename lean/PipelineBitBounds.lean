import CoefficientBounds
import WalshEmbedding
import HighBoxDP
import SharedEncoder
import CompleteThinProduct

/-!
# Coefficient budgets for the actual source and stored-array pipeline

Theorems in this module start with bounded original input coefficients.
They propagate bounds through the literal Walsh source formulas, the sparse
normal/opposite polynomial rows, shared materialized dense arrays, and the
stored HIGH table.  Bounds concern all cyclic coefficient slots and every
auxiliary degree, rather than a selected requested coefficient.
-/

namespace ThinMatrix.PipelineBitBounds

open scoped BigOperators
open CyclicRing CoefficientBounds WalshEmbedding LinearCircuitBound

attribute [local instance] Classical.propDecidable

 theorem character_abs (k : ℕ) (a x : Cube k) :
    |character (R := ℤ) a x| = 1 := by
  simp only [character, Finset.abs_prod]
  have h (i : Fin k) : |bitChar (R := ℤ) (a i) (x i)| = 1 := by
    unfold bitChar
    split_ifs <;> norm_num
  simp only [h, Finset.prod_const_one]

 theorem character_intCast {q k : ℕ} [NeZero q] (a x : Cube k) :
    character (R := Cyclic q) a x = ((character (R := ℤ) a x : ℤ) : Cyclic q) := by
  unfold character
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  unfold bitChar
  split_ifs <;> simp

 theorem walsh_coefficient_bound {q k A : ℕ} [NeZero q]
    (f : Cube k → Cyclic q) (hf : ∀ x, CoeffBound (f x) A) (a : Cube k) :
    CoeffBound (walsh f a) (2^k*A) := by
  intro j
  unfold walsh
  simp_rw [character_intCast, sum_coeff, intCast_mul_coeff]
  calc
    |∑ x : Cube k, character (R := ℤ) a x * f x j| ≤
        ∑ x : Cube k, |character (R := ℤ) a x * f x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x : Cube k, |f x j| := by simp only [abs_mul, character_abs, one_mul]
    _ ≤ ∑ _x : Cube k, (A : ℤ) := Finset.sum_le_sum (fun x _ => hf x j)
    _ = (2^k*A : ℕ) := by simp [Cube]

 theorem normalP2_ones_le_support {L : ℕ} (normal : Fin L → NormalLetter) :
    ones (normalP2Bits normal) ≤ (normalSupport normal).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [normalP2Bits, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq] at hi
  simp [normalSupport, normalIsP, hi]

 theorem rawLeftSource_bound {q L m k A : ℕ} [NeZero q]
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hX : ∀ Q a b r s, CoeffBound (X Q a b r s) A)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    CoeffBound (rawLeftSource X good gamma delta run normal opposite) (2^(k+m)*A) := by
  unfold rawLeftSource
  split_ifs with h
  · have hw : ones (normalP2Bits normal) ≤ m := by
      rw [← hgood _ h.1]
      exact normalP2_ones_le_support normal
    have h := source_weight_bound
      (walsh (fun outer => X (normalSupport normal) (normalOuterBits normal) outer
        (gamma (normalP2Bits normal)) (gamma (oppositeWBits opposite)))
        (delta (oppositeVBits opposite))) m (ones (normalP2Bits normal)) (2^k*A)
      hw (walsh_coefficient_bound _ (fun outer => hX _ _ outer _ _) _)
    intro j
    simpa [scale, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      ← intCast_mul_coeff] using h j
  · intro j
    simp

 theorem rawRightSource_bound {q L m k A : ℕ} [NeZero q]
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hY : ∀ Q a r s b, CoeffBound (Y Q a r s b) A)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    CoeffBound (rawRightSource Y good gamma delta run normal opposite) (2^(k+m)*A) := by
  unfold rawRightSource
  split_ifs with h
  · have hw : ones (normalP2Bits normal) ≤ m := by
      rw [← hgood _ h.1]
      exact normalP2_ones_le_support normal
    have h := source_weight_bound
      (walsh (fun outer => Y (normalSupport normal) (normalOuterBits normal)
        (gamma (oppositeWBits opposite)) (gamma (normalP2Bits normal)) outer)
        (delta (oppositeVBits opposite))) m (ones (normalP2Bits normal)) (2^k*A)
      hw (walsh_coefficient_bound _ (fun outer => hY _ _ _ _ outer) _)
    intro j
    simpa [scale, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      ← intCast_mul_coeff] using h j
  · intro j
    simp


/-- Every formal auxiliary degree and every cyclic slot is covered. -/
def PolynomialCoeffBound {q : ℕ} [NeZero q] (p : Polynomial (Cyclic q)) (A : ℕ) : Prop :=
  ∀ d, CoeffBound (p.coeff d) A

/-- The literal six sparse cache forms: the single `p₁` coefficient of
`H(z)` reads the preceding auxiliary degree. All other rows are constant. -/
noncomputable def localPolynomial {q : ℕ} [NeZero q] (normal : Bool)
    (row : Fin 6) (col : Fin 4) : Polynomial (Cyclic q) :=
  if normal ∧ row = 4 ∧ col = 2 then Polynomial.X
  else Polynomial.C ((if normal then normalRowCoefficients row col
    else oppositeRowCoefficients row col : ℤ) : Cyclic q)

 theorem localPolynomial_mul_bound {q A : ℕ} [NeZero q]
    (normal : Bool) (row : Fin 6) (col : Fin 4) (p : Polynomial (Cyclic q))
    (hp : PolynomialCoeffBound p A) :
    PolynomialCoeffBound (localPolynomial normal row col * p) (2*A) := by
  intro d k
  by_cases h : normal ∧ row = 4 ∧ col = 2
  · rw [localPolynomial, if_pos h]
    cases d with
    | zero => simp
    | succ d =>
      rw [Polynomial.coeff_X_mul]
      exact (hp d k).trans (by exact_mod_cast Nat.le_mul_of_pos_left A (by decide : 0 < 2))
  · rw [localPolynomial, if_neg h, Polynomial.coeff_C_mul, intCast_mul_coeff, abs_mul]
    have hc : |(if normal then normalRowCoefficients row col
        else oppositeRowCoefficients row col : ℤ)| ≤ 2 := by
      cases normal
      · exact oppositeRowCoefficients_bound row col
      · exact normalRowCoefficients_bound row col
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      mul_le_mul hc (hp d k) (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 2)

/-- The shared encoder receives the actual polynomial rows, with a zero
padding column only outside the four-letter local alphabet. -/
noncomputable def cacheForms {q : ℕ} [NeZero q] (normalAt : ℕ → Bool) :
    SharedEncoder.LocalForms (Polynomial (Cyclic q)) :=
  fun d row col => if h : col < 4 then localPolynomial (normalAt d) row ⟨col,h⟩ else 0

set_option maxHeartbeats 1000000 in
 theorem contract_stored_bound {q n A : ℕ} [NeZero q]
    (dims : Fin (n+1) → ℕ) (hdims : dims 0 ≤ 4)
    (normal : Bool) (row : Fin 6)
    (input : SharedEncoder.Dense (R := Polynomial (Cyclic q)) (n+1) dims)
    (hinput : ∀ a, PolynomialCoeffBound (SharedEncoder.read (n+1) dims input a) A) :
    ∀ rest, PolynomialCoeffBound
      (SharedEncoder.read n (fun i => dims i.succ)
        (SharedEncoder.contract dims
          (fun a => localPolynomial normal row ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩) input) rest)
      (8*A) := by
  intro rest d k
  rw [SharedEncoder.read_contract]
  simp only [EncoderCorrectness.contractFirst, Polynomial.finsetSum_coeff, sum_coeff]
  calc
    |∑ a : Fin (dims 0), ((localPolynomial normal row
          ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩ *
          SharedEncoder.read (n+1) dims input (Fin.cons a rest)).coeff d) k| ≤
        ∑ a : Fin (dims 0), |((localPolynomial normal row
          ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩ *
          SharedEncoder.read (n+1) dims input (Fin.cons a rest)).coeff d) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin (dims 0), (2*(A : ℤ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact localPolynomial_mul_bound normal row _ _ (hinput _) d k
    _ = ((dims 0 : ℤ)*(2*(A : ℤ))) := by simp
    _ ≤ (8*A : ℕ) := by exact_mod_cast (show (dims 0)*(2*A) ≤ 8*A by nlinarith)


/-- Any partial HIGH leaf accumulation is bounded by the complete number
of formal five-letter words, including cancellations and zero leaves. -/
 theorem partial_high_leaf_sum_bound {q n A : ℕ} [NeZero q]
    (leaf : HighBoxDP.LeafWord n → Cyclic q)
    (hleaf : ∀ v, CoeffBound (leaf v) A) (s : Finset (HighBoxDP.LeafWord n)) :
    CoeffBound (fun k => ∑ v ∈ s, leaf v k) (5^n*A) := by
  have h := finite_sum_bound s leaf A (fun v _ => hleaf v)
  apply h.mono
  apply Nat.mul_le_mul_right
  simpa [HighBoxDP.LeafWord] using s.card_le_univ

 theorem high_box_bound {q n A : ℕ} [NeZero q]
    (leaf : HighBoxDP.LeafWord n → Cyclic q)
    (hleaf : ∀ v, CoeffBound (leaf v) A) (w : CacheBounds.Word n) :
    CoeffBound (HighBoxDP.boxValue w leaf) (5^n*A) := by
  intro k
  unfold HighBoxDP.boxValue
  rw [sum_coeff]
  have h := partial_high_leaf_sum_bound leaf hleaf
    (Finset.univ.filter (HighBoxDP.Compatible w)) k
  have he : (∑ v : HighBoxDP.LeafWord n,
      (if HighBoxDP.Compatible w v then leaf v else (0 : Cyclic q)) k) =
      ∑ v : HighBoxDP.LeafWord n, if HighBoxDP.Compatible w v then leaf v k else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hc : HighBoxDP.Compatible w v <;> simp [hc]
  rw [he]
  simpa only [Finset.sum_filter] using h

 theorem tableAfter_zero_above {L m t : ℕ} {R : Type*} [AddCommMonoid R]
    (leaf : HighBoxDP.LeafWord (2*L) → R) (k : ℕ) (w : HighBoxDP.States L m t)
    (hw : k ≤ HighBoxDP.starCount w.val) : HighBoxDP.tableAfter leaf k w = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [HighBoxDP.tableAfter, HighBoxDP.updateLayer]
    rw [if_neg (by omega)]
    exact ih (by omega)

/-- Every address at every point of the actual bottom-up HIGH schedule is
either unwritten zero or its exact box. No bound on the stored table is
assumed as a premise. -/
 theorem every_high_table_bound {q L m t A : ℕ} [NeZero q]
    (leaf : HighBoxDP.LeafWord (2*L) → Cyclic q)
    (hleaf : ∀ v, CoeffBound (leaf v) A) (k : ℕ) (w : HighBoxDP.States L m t) :
    CoeffBound (HighBoxDP.tableAfter leaf k w) (5^(2*L)*A) := by
  by_cases hw : HighBoxDP.starCount w.val < k
  · rw [HighBoxDP.tableAfter_correct_below leaf k w hw]
    exact high_box_bound leaf hleaf w.val
  · rw [tableAfter_zero_above leaf k w (by omega)]
    intro j
    simp

 theorem high_product_table_bound {q L m t A B : ℕ} [NeZero q]
    (left right : HighBoxDP.LeafWord (2*L) → Cyclic q)
    (hleft : ∀ v, CoeffBound (left v) A) (hright : ∀ v, CoeffBound (right v) B)
    (k : ℕ) (w : HighBoxDP.States L m t) :
    CoeffBound (HighBoxDP.tableAfter (HighBoxDP.productLeaf left right) k w)
      (5^(2*L)*(q*A*B)) :=
  every_high_table_bound (HighBoxDP.productLeaf left right)
    (fun v => leaf_product_bound _ _ (hleft v) (hright v)) k w


 theorem PolynomialCoeffBound.mono {q A B : ℕ} [NeZero q]
    {p : Polynomial (Cyclic q)} (h : PolynomialCoeffBound p A) (hAB : A ≤ B) :
    PolynomialCoeffBound p B := fun d => (h d).mono hAB

 theorem constantPolynomial_bound {q A : ℕ} [NeZero q] (a : Cyclic q)
    (ha : CoeffBound a A) : PolynomialCoeffBound (Polynomial.C a) A := by
  intro d k
  cases d with
  | zero => simpa using ha k
  | succ d => simp

/-- A depth-indexed invariant on the genuine stored dense arrays. -/
def StoredBound {q : ℕ} [NeZero q] (L A d n : ℕ) (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := Polynomial (Cyclic q)) (2*L) n dims) : Prop :=
  d+n=2*L ∧ (∀ i, dims i ≤ 4) ∧
    ∀ a, PolynomialCoeffBound (SharedEncoder.read n dims node.data a) (8^d*A)

set_option maxHeartbeats 1000000 in
 theorem storedBound_step {q L m t A d n : ℕ} [NeZero q]
    (normalAt : ℕ → Bool) (hd : d < 2*L) (dims : Fin (n+1) → ℕ)
    (parent : SharedEncoder.Node (R := Polynomial (Cyclic q)) (2*L) (n+1) dims)
    (hp : StoredBound L A d (n+1) dims parent) :
    ∀ child ∈ SharedEncoder.nodeChildren L m t d n hd dims (cacheForms normalAt) parent,
      StoredBound L A (d+1) n (fun i => dims i.succ) child := by
  intro child hc
  obtain ⟨row, hcap, rfl⟩ := (SharedEncoder.mem_nodeChildren L m t d n hd dims
    (cacheForms normalAt) parent child).mp hc
  refine ⟨by have := hp.1; omega, fun i => hp.2.1 i.succ, ?_⟩
  intro rest
  have hform : (fun a : Fin (dims 0) => cacheForms (q := q) normalAt d row a.val) =
      fun a : Fin (dims 0) => localPolynomial (normalAt d) row
        ⟨a.val, lt_of_lt_of_le a.isLt (hp.2.1 0)⟩ := by
    funext a
    simp only [cacheForms, dif_pos (lt_of_lt_of_le a.isLt (hp.2.1 0))]
  simp only [hform]
  have h := contract_stored_bound dims (hp.2.1 0) (normalAt d) row parent.data hp.2.2 rest
  have he : 8*(8^d*A)=8^(d+1)*A := by rw [pow_succ]; ring
  simpa only [he] using h

set_option maxHeartbeats 1000000 in
/-- All materialized intermediate cells in the actual shared-prefix run
are bounded from the original dense input. The statement quantifies over
the returned `formed` trace, not independent leaf recomputations. -/
 theorem shared_run_stored_bound {q L m t A : ℕ} [NeZero q]
    (width : ℕ) (normalAt : ℕ → Bool) (dims : Fin (2*L) → ℕ)
    (hdims : ∀ i, dims i ≤ 4) (input : SharedEncoder.Coordinates dims → Polynomial (Cyclic q))
    (hinput : ∀ a, PolynomialCoeffBound (input a) A) :
    ∀ s ∈ (SharedEncoder.run L m t q width (cacheForms normalAt) (2*L) dims 0
      [⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩]).formed,
      ∀ a, PolynomialCoeffBound
        (SharedEncoder.read s.remaining s.dims s.node.data a) (2^(6*L)*A) := by
  have hroot : ∀ parent ∈ ([⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩] :
      List (SharedEncoder.Node (R := Polynomial (Cyclic q)) (2*L) (2*L) dims)),
      StoredBound L A 0 (2*L) dims parent := by
    intro parent hp
    simp only [List.mem_singleton] at hp
    subst parent
    refine ⟨by omega, hdims, ?_⟩
    intro a
    simpa only [SharedEncoder.read_materialize, pow_zero, one_mul] using hinput a
  have h := SharedEncoder.run_invariant L m t q width (cacheForms normalAt)
    (StoredBound L A) (fun d n hd dims parent hp =>
      storedBound_step normalAt hd dims parent hp) (2*L) dims 0 _ hroot
  intro s hs a
  have hb := h s hs
  apply (hb.2.2 a).mono
  have hdepth : s.depth ≤ 2*L := by have := hb.1; omega
  have hp : 8^s.depth ≤ 2^(6*L) := by
    calc
      8^s.depth = (2^3)^s.depth := by norm_num
      _ = 2^(3*s.depth) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.mul_le_mul_right A hp


/-- The actual input-polynomial source values fit the uniform source
budget. Letter parsers are arbitrary here: this bound does not use or
assume the separate coordinate-bijection correctness theorem. -/
 theorem rawLeftPolynomial_bound {q L m k A : ℕ} [NeZero q]
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hX : ∀ Q a b r s, CoeffBound (X Q a b r s) A)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (hk : k ≤ L) :
    PolynomialCoeffBound (Polynomial.C (rawLeftSource X good gamma delta run normal opposite))
      (2^(L+m)*A) := by
  apply (constantPolynomial_bound _
    (rawLeftSource_bound X good gamma delta run hgood hX normal opposite)).mono
  exact Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega))

 theorem rawRightPolynomial_bound {q L m k A : ℕ} [NeZero q]
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hY : ∀ Q a r s b, CoeffBound (Y Q a r s b) A)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (hk : k ≤ L) :
    PolynomialCoeffBound (Polynomial.C (rawRightSource Y good gamma delta run normal opposite))
      (2^(L+m)*A) := by
  apply (constantPolynomial_bound _
    (rawRightSource_bound Y good gamma delta run hgood hY normal opposite)).mono
  exact Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The concrete HIGH table, when its bases are genuine transformed-source
products, has the same uniform budget as the LOW numerator. -/
 theorem encoded_high_table_uniform_bound {q L m t A : ℕ} [NeZero q]
    (left right : HighBoxDP.LeafWord (2*L) → Cyclic q)
    (hleft : ∀ v, CoeffBound (left v) (2^(7*L+m)*A))
    (hright : ∀ v, CoeffBound (right v) (2^(7*L+m)*A))
    (k : ℕ) (w : HighBoxDP.States L m t) :
    CoeffBound (HighBoxDP.tableAfter (HighBoxDP.productLeaf left right) k w)
      (uniformBudget L m t q A) := by
  have h := high_product_table_bound left right hleft hright k w
  apply h.mono
  calc
    5^(2*L)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)) ≤
        (2^3)^(2*L)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)) := by gcongr; norm_num
    _ = q*2^(20*L+2*m)*A^2 := by
      rw [← pow_mul, show 20*L+2*m=3*(2*L)+(7*L+m)+(7*L+m) by omega]
      simp only [pow_add]
      ring
    _ ≤ _ := quadratic_le_uniform L m t q A (20*L+2*m) (by omega)

set_option maxHeartbeats 1000000 in
 theorem shared_run_uniform_bound {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (normalAt : ℕ → Bool) (dims : Fin (2*L) → ℕ)
    (hdims : ∀ i, dims i ≤ 4) (input : SharedEncoder.Coordinates dims → Polynomial (Cyclic q))
    (hinput : ∀ a, PolynomialCoeffBound (input a) (2^(L+m)*A)) :
    ∀ s ∈ (SharedEncoder.run L m t q width (cacheForms normalAt) (2*L) dims 0
      [⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩]).formed,
      ∀ a d, CoeffBound
        ((SharedEncoder.read s.remaining s.dims s.node.data a).coeff d)
        (uniformBudget L m t q A) := by
  intro s hs a d
  have h := shared_run_stored_bound width normalAt dims hdims input hinput s hs a d
  apply h.mono
  have he : 2^(6*L)*(2^(L+m)*A)=2^(7*L+m)*A := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [he]
  exact linear_le_uniform L m t q A (7*L+m)
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hA (by omega)

set_option maxHeartbeats 1000000 in
 theorem every_cache_coefficient_bits {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (normalAt : ℕ → Bool) (dims : Fin (2*L) → ℕ)
    (hdims : ∀ i, dims i ≤ 4) (input : SharedEncoder.Coordinates dims → Polynomial (Cyclic q))
    (hinput : ∀ a, PolynomialCoeffBound (input a) (2^(L+m)*A))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) :
    ∀ s ∈ (SharedEncoder.run L m t q width (cacheForms normalAt) (2*L) dims 0
      [⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩]).formed,
      ∀ a d j, CoefficientBudget.signedBitLength
        ((SharedEncoder.read s.remaining s.dims s.node.data a).coeff d j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  intro s hs a d j
  exact coeffBound_signedBitLength _
    (shared_run_uniform_bound hA width normalAt dims hdims input hinput s hs a d)
    r cL cm cq cA hL hm hq hAb ht j

 theorem every_high_coefficient_bits {q L m t A : ℕ} [NeZero q]
    (left right : HighBoxDP.LeafWord (2*L) → Cyclic q)
    (hleft : ∀ v, CoeffBound (left v) (2^(7*L+m)*A))
    (hright : ∀ v, CoeffBound (right v) (2^(7*L+m)*A))
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m)
    (k : ℕ) (w : HighBoxDP.States L m t) (j : Fin q) :
    CoefficientBudget.signedBitLength
      (HighBoxDP.tableAfter (HighBoxDP.productLeaf left right) k w j) ≤
      CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 :=
  coeffBound_signedBitLength _ (encoded_high_table_uniform_bound left right hleft hright k w)
    r cL cm cq cA hL hm hq hAb ht j


 theorem polynomial_product_coefficient_bound {q A B : ℕ} [NeZero q]
    (p r : Polynomial (Cyclic q)) (hp : PolynomialCoeffBound p A)
    (hr : PolynomialCoeffBound r B) (d : ℕ) :
    CoeffBound ((p*r).coeff d) ((d+1)*(q*A*B)) := by
  rw [Polynomial.coeff_mul]
  have h := finite_sum_bound (Finset.antidiagonal d)
    (fun ij => p.coeff ij.1 * r.coeff ij.2) (q*A*B)
    (fun ij _ => leaf_product_bound _ _ (hp ij.1) (hr ij.2))
  intro k
  simpa only [sum_coeff, Finset.Nat.card_antidiagonal] using h k

 theorem residualWeight_intCast {q : ℕ} [NeZero q] (m t j : ℕ) :
    TensorContraction.residualWeight (R := Cyclic q) (2*m) t j =
      ((a11Weight m t j : ℤ) : Cyclic q) := by
  simp [TensorContraction.residualWeight, a11Weight]

/-- The actual cached LOW functional: same physical channel key on both
sides, one global shift `j-|C|`, and all cyclic coefficients retained. -/
noncomputable def cachedLow {q m t : ℕ} [NeZero q]
    (keys : Finset (Finset (Fin (2*m))))
    (left right : Finset (Fin (2*m)) → Polynomial (Cyclic q)) : Cyclic q :=
  ∑ C ∈ keys, ∑ j ∈ Finset.range t,
    if C.card ≤ j then TensorContraction.residualWeight (2*m) t j *
      (left C * right C).coeff (j-C.card) else 0

set_option maxHeartbeats 1000000 in
 theorem cachedLow_bound {q L m t A : ℕ} [NeZero q]
    (keys : Finset (Finset (Fin (2*m)))) (hkeys : keys.card ≤ 2^(2*m))
    (left right : Finset (Fin (2*m)) → Polynomial (Cyclic q))
    (hleft : ∀ C ∈ keys, PolynomialCoeffBound (left C) (2^(7*L+m)*A))
    (hright : ∀ C ∈ keys, PolynomialCoeffBound (right C) (2^(7*L+m)*A)) :
    CoeffBound (cachedLow (t := t) keys left right) (q*(t+1)^2*2^(14*L+6*m)*A^2) := by
  let term := fun C j => if C.card ≤ j then
    TensorContraction.residualWeight (R := Cyclic q) (2*m) t j *
      (left C * right C).coeff (j-C.card) else 0
  have ht (C : Finset (Fin (2*m))) (hC : C ∈ keys) (j : ℕ) (hj : j ∈ Finset.range t) :
      CoeffBound (term C j) (2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))) := by
    unfold term
    split_ifs with h
    · rw [residualWeight_intCast]
      have hp := polynomial_product_coefficient_bound (left C) (right C)
        (hleft C hC) (hright C hC) (j-C.card)
      have hdeg : (j-C.card+1) ≤ t+1 := by
        have := Finset.mem_range.mp hj
        omega
      have hp' := hp.mono (Nat.mul_le_mul_right _ hdeg)
      intro k
      have hb := scale_bound (a11Weight m t j) ((left C*right C).coeff (j-C.card))
        (a11Weight_bound m t j) hp' k
      simpa only [scale, intCast_mul_coeff] using hb
    · intro k
      simp only [zero_coeff, abs_zero]
      positivity
  have hinner (C : Finset (Fin (2*m))) (hC : C ∈ keys) :=
    finite_sum_bound (Finset.range t) (term C)
      (2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))) (ht C hC)
  have hinner' (C : Finset (Fin (2*m))) (hC : C ∈ keys) :
      CoeffBound (fun k => ∑ j ∈ Finset.range t, term C j k)
      ((t+1)*(2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A))))) :=
    (hinner C hC).mono (by simp only [Finset.card_range]; exact Nat.mul_le_mul_right _ (by omega))
  have hsum := finite_sum_bound keys
    (fun C k => ∑ j ∈ Finset.range t, term C j k)
    ((t+1)*(2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A))))) hinner'
  have hsum' := hsum.mono (Nat.mul_le_mul_right _ hkeys)
  have he : 2^(2*m)*((t+1)*(2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A))))) =
      q*(t+1)^2*2^(14*L+6*m)*A^2 := by
    rw [show 14*L+6*m=2*m+(2*m+((7*L+m)+(7*L+m))) by omega]
    simp only [pow_add]
    ring
  intro k
  simpa only [cachedLow, sum_coeff, he, term] using hsum' k


set_option maxHeartbeats 1000000 in
/-- End-to-end bit bound for the original left input, its exact weighted
Walsh source, and every materialized cache intermediate. Only original
input coefficients and structural size hypotheses occur as premises. -/
 theorem original_left_cache_bits {q L m k t A : ℕ} [NeZero q]
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hX : ∀ Q a b r s, CoeffBound (X Q a b r s) A) (hk : k ≤ L) (hA : 1 ≤ A)
    (width : ℕ) (normalAt : ℕ → Bool) (dims : Fin (2*L) → ℕ) (hdims : ∀ i, dims i ≤ 4)
    (normal : SharedEncoder.Coordinates dims → Fin L → NormalLetter)
    (opposite : SharedEncoder.Coordinates dims → Fin L → OppositeLetter)
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) :
    let input := fun a => Polynomial.C (rawLeftSource X good gamma delta run (normal a) (opposite a))
    ∀ s ∈ (SharedEncoder.run L m t q width (cacheForms normalAt) (2*L) dims 0
      [⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩]).formed,
      ∀ a d j, CoefficientBudget.signedBitLength
        ((SharedEncoder.read s.remaining s.dims s.node.data a).coeff d j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  dsimp only
  apply every_cache_coefficient_bits hA width normalAt dims hdims _ _
    r cL cm cq cA hL hm hq hAb ht
  intro a
  exact rawLeftPolynomial_bound X good gamma delta run hgood hX (normal a) (opposite a) hk

set_option maxHeartbeats 1000000 in
 theorem original_right_cache_bits {q L m k t A : ℕ} [NeZero q]
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (gamma : Cube L → Cube m) (delta : Cube L → Cube k) (run : ℤ)
    (hgood : ∀ Q ∈ good, Q.card = m)
    (hY : ∀ Q a r s b, CoeffBound (Y Q a r s b) A) (hk : k ≤ L) (hA : 1 ≤ A)
    (width : ℕ) (normalAt : ℕ → Bool) (dims : Fin (2*L) → ℕ) (hdims : ∀ i, dims i ≤ 4)
    (normal : SharedEncoder.Coordinates dims → Fin L → NormalLetter)
    (opposite : SharedEncoder.Coordinates dims → Fin L → OppositeLetter)
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m) :
    let input := fun a => Polynomial.C (rawRightSource Y good gamma delta run (normal a) (opposite a))
    ∀ s ∈ (SharedEncoder.run L m t q width (cacheForms normalAt) (2*L) dims 0
      [⟨fun _ => 0, SharedEncoder.materialize (2*L) dims input⟩]).formed,
      ∀ a d j, CoefficientBudget.signedBitLength
        ((SharedEncoder.read s.remaining s.dims s.node.data a).coeff d j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 := by
  dsimp only
  apply every_cache_coefficient_bits hA width normalAt dims hdims _ _
    r cL cm cq cA hL hm hq hAb ht
  intro a
  exact rawRightPolynomial_bound Y good gamma delta run hgood hY (normal a) (opposite a) hk


 theorem normalForm_intCast {q : ℕ} [NeZero q] (n : NormalLetter) (l : Fin 5) :
    CompleteThinProduct.normalForm (R := Cyclic q) n l =
      ((CompleteThinProduct.normalForm (R := ℤ) n l : ℤ) : Cyclic q) := by
  cases n <;> fin_cases l <;>
    norm_num [CompleteThinProduct.normalForm, TensorContraction.alignedLeft,
      CompleteThinProduct.letterIndicator, reduceCtorEq]

 theorem oppositeForm_intCast {q : ℕ} [NeZero q] (o : OppositeLetter) (l : Fin 5) :
    CompleteThinProduct.oppositeForm (R := Cyclic q) o l =
      ((CompleteThinProduct.oppositeForm (R := ℤ) o l : ℤ) : Cyclic q) := by
  cases o <;> fin_cases l <;>
    norm_num [CompleteThinProduct.oppositeForm, TensorContraction.alignedRight,
      CompleteThinProduct.letterIndicator, reduceCtorEq]

 theorem normalForm_abs (n : NormalLetter) (l : Fin 5) :
    |CompleteThinProduct.normalForm (R := ℤ) n l| ≤ 2 := by
  cases n <;> fin_cases l <;> decide

 theorem oppositeForm_abs (o : OppositeLetter) (l : Fin 5) :
    |CompleteThinProduct.oppositeForm (R := ℤ) o l| ≤ 2 := by
  cases o <;> fin_cases l <;> decide

 theorem sourceF_intCast {q L : ℕ} [NeZero q] (i : Fin (2*L))
    (l : Fin 5) (a : CompleteThinProduct.SourceWord L) :
    CompleteThinProduct.sourceF (R := Cyclic q) i l a =
      ((CompleteThinProduct.sourceF (R := ℤ) i l a : ℤ) : Cyclic q) := by
  simp only [CompleteThinProduct.sourceF, CompleteThinProduct.halfLift]
  split <;> simp only [normalForm_intCast, oppositeForm_intCast]

 theorem sourceG_intCast {q L : ℕ} [NeZero q] (i : Fin (2*L))
    (l : Fin 5) (a : CompleteThinProduct.SourceWord L) :
    CompleteThinProduct.sourceG (R := Cyclic q) i l a =
      ((CompleteThinProduct.sourceG (R := ℤ) i l a : ℤ) : Cyclic q) := by
  simp only [CompleteThinProduct.sourceG, CompleteThinProduct.halfLift]
  split <;> simp only [normalForm_intCast, oppositeForm_intCast]

 theorem sourceF_abs {L : ℕ} (i : Fin (2*L)) (l : Fin 5)
    (a : CompleteThinProduct.SourceWord L) :
    |CompleteThinProduct.sourceF (R := ℤ) i l a| ≤ 2 := by
  simp only [CompleteThinProduct.sourceF, CompleteThinProduct.halfLift]
  split
  · exact normalForm_abs _ _
  · exact oppositeForm_abs _ _

 theorem sourceG_abs {L : ℕ} (i : Fin (2*L)) (l : Fin 5)
    (a : CompleteThinProduct.SourceWord L) :
    |CompleteThinProduct.sourceG (R := ℤ) i l a| ≤ 2 := by
  simp only [CompleteThinProduct.sourceG, CompleteThinProduct.halfLift]
  split
  · exact oppositeForm_abs _ _
  · exact normalForm_abs _ _

 theorem sourceWord_card (L : ℕ) : Fintype.card (CompleteThinProduct.SourceWord L) = 12^L := by
  have hn : Fintype.card NormalLetter = 4 := by decide
  have ho : Fintype.card OppositeLetter = 3 := by decide
  simp only [CompleteThinProduct.SourceWord, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, hn, ho, ← mul_pow]
  norm_num

/-- A literal full physical source transform. This is the denotation of a
stored cache leaf; the proof does not rerun the transform to charge its cost. -/
 theorem source_transform_bound {q L A : ℕ} [NeZero q]
    (src : CompleteThinProduct.SourceWord L → Cyclic q)
    (hsrc : ∀ a, CoeffBound (src a) A)
    (f : Fin (2*L) → Fin 5 → CompleteThinProduct.SourceWord L → ℤ)
    (hf : ∀ i l a, |f i l a| ≤ 2) (v : HighBoxDP.LeafWord (2*L)) :
    CoeffBound (∑ a, src a * ∏ i, ((f i (v i) a : ℤ) : Cyclic q)) (2^(6*L)*A) := by
  have hterm (a : CompleteThinProduct.SourceWord L) :
      CoeffBound (src a * ∏ i, ((f i (v i) a : ℤ) : Cyclic q)) (2^(2*L)*A) := by
    intro k
    rw [← Int.cast_prod, mul_comm, intCast_mul_coeff, abs_mul, Finset.abs_prod]
    have hp : (∏ i : Fin (2*L), |f i (v i) a|) ≤ (2 : ℤ)^(2*L) := by
      calc
        _ ≤ ∏ _i : Fin (2*L), (2 : ℤ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hf i _ _)
        _ = _ := by simp
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul hp (hsrc a k) (abs_nonneg _) (by positivity : (0 : ℤ) ≤ 2^(2*L))
  have hsum := finite_sum_bound Finset.univ _ (2^(2*L)*A) (fun a _ => hterm a)
  have hcard : (Finset.univ : Finset (CompleteThinProduct.SourceWord L)).card ≤ 2^(4*L) := by
    rw [Finset.card_univ, sourceWord_card]
    calc
      12^L ≤ (2^4)^L := Nat.pow_le_pow_left (by norm_num) L
      _ = _ := (pow_mul _ _ _).symm
  have hn : (Finset.univ : Finset (CompleteThinProduct.SourceWord L)).card * (2^(2*L)*A) ≤
      2^(6*L)*A := by
    calc
      _ ≤ 2^(4*L)*(2^(2*L)*A) := Nat.mul_le_mul_right _ hcard
      _ = _ := by rw [← mul_assoc, ← pow_add]; congr 2; omega
  intro k
  have h := (hsum.mono hn) k
  simpa only [sum_coeff] using h

 theorem actual_global_leaf_bound {q L m k A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hgood : ∀ Q ∈ d.good, Q.card = m) (hk : k ≤ L)
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (run : ℤ) (v : HighBoxDP.LeafWord (2*L)) :
    CoeffBound (CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
      CompleteThinProduct.sourceF CompleteThinProduct.sourceG v)
      (q*2^(14*L+2*m)*A^2) := by
  have hl (a : CompleteThinProduct.SourceWord L) : CoeffBound (d.leftRun run a) (2^(L+m)*A) := by
    have h := rawLeftSource_bound d.X d.good d.gamma d.delta run hgood hX a.1 a.2
    exact h.mono (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hr (a : CompleteThinProduct.SourceWord L) : CoeffBound (d.rightRun run a) (2^(L+m)*A) := by
    have h := rawRightSource_bound d.Y d.good d.gamma d.delta run hgood hY a.1 a.2
    exact h.mono (Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hleft := source_transform_bound (d.leftRun run) hl
    (CompleteThinProduct.sourceF (R := ℤ)) sourceF_abs v
  have hright := source_transform_bound (d.rightRun run) hr
    (CompleteThinProduct.sourceG (R := ℤ)) sourceG_abs v
  simp only [← sourceF_intCast] at hleft
  simp only [← sourceG_intCast] at hright
  have he : 2^(6*L)*(2^(L+m)*A)=2^(7*L+m)*A := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [he] at hleft hright
  have h := leaf_product_bound _ _ hleft hright
  have hb : q*(2^(7*L+m)*A)*(2^(7*L+m)*A)=q*2^(14*L+2*m)*A^2 := by
    rw [show 14*L+2*m=(7*L+m)+(7*L+m) by omega, pow_add]
    ring
  simpa only [CompleteThinProduct.globalLeaf, hb] using h

/-- Every HIGH table coefficient for the actual unnormalized Walsh source
pipeline is bounded from original input coefficients alone. -/
 theorem actual_high_table_uniform_bound {q L m k t A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hgood : ∀ Q ∈ d.good, Q.card = m) (hk : k ≤ L)
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (run : ℤ) (stage : ℕ) (w : HighBoxDP.States L m t) :
    CoeffBound (HighBoxDP.tableAfter
      (CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) stage w)
      (uniformBudget L m t q A) := by
  have h := every_high_table_bound _ (actual_global_leaf_bound d hgood hk hX hY run) stage w
  apply h.mono
  calc
    5^(2*L)*(q*2^(14*L+2*m)*A^2) ≤ (2^3)^(2*L)*(q*2^(14*L+2*m)*A^2) := by gcongr; norm_num
    _ = q*2^(20*L+2*m)*A^2 := by
      rw [← pow_mul, show 20*L+2*m=3*(2*L)+(14*L+2*m) by omega, pow_add]
      ring
    _ ≤ _ := quadratic_le_uniform L m t q A (20*L+2*m) (by omega)


 theorem actual_high_coefficient_bits {q L m k t A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hgood : ∀ Q ∈ d.good, Q.card = m) (hk : k ≤ L)
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (r cL cm cq cA : ℕ) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (hq : q ≤ 2^(cq*r)) (hAb : A ≤ 2^(cA*r)) (ht : t ≤ 2*m)
    (run : ℤ) (stage : ℕ) (w : HighBoxDP.States L m t) (j : Fin q) :
    CoefficientBudget.signedBitLength (HighBoxDP.tableAfter
      (CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) stage w j) ≤
        CoefficientBudget.budgetConstant cL cm cq cA*(r+1)+2 :=
  coeffBound_signedBitLength _ (actual_high_table_uniform_bound d hgood hk hX hY run stage w)
    r cL cm cq cA hL hm hq hAb ht j

 theorem actual_matrix_product_bound {q L m k A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A) (aL aR : Cube k) :
    CoeffBound (d.matrixProductEntry aL aR) (q*2^(2*m)*A^2) := by
  have hinner (h1 : Cube m) := finite_sum_bound Finset.univ
    (fun h2 : Cube m => d.X d.QL (outsideBits d.QL d.iL) aL h1 h2 *
      d.Y d.QR (outsideBits d.QR d.iR) h1 h2 aR) (q*A*A)
    (fun h2 _ => leaf_product_bound _ _ (hX _ _ _ _ _) (hY _ _ _ _ _))
  have hinner' (h1 : Cube m) : CoeffBound
      (∑ h2 : Cube m, d.X d.QL (outsideBits d.QL d.iL) aL h1 h2 *
        d.Y d.QR (outsideBits d.QR d.iR) h1 h2 aR) (2^m*(q*A*A)) := by
    intro j
    simpa [Cube] using hinner h1 j
  have houter := finite_sum_bound Finset.univ
    (fun h1 : Cube m => ∑ h2 : Cube m, d.X d.QL (outsideBits d.QL d.iL) aL h1 h2 *
      d.Y d.QR (outsideBits d.QR d.iR) h1 h2 aR) (2^m*(q*A*A)) (fun h1 _ => hinner' h1)
  have he : 2^m*(2^m*(q*A*A))=q*2^(2*m)*A^2 := by
    rw [show 2*m=m+m by omega, pow_add]
    ring
  intro j
  simpa [CompleteThinProduct.SourceQueryData.matrixProductEntry, Cube, he] using houter j

 theorem actual_complete_numerator_bound {q L m k t A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (ht : t ≤ 2*m) (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta=columnMap columns)
    (hjL : d.jL=transposeMap columns aR) (hjR : d.jR=transposeMap columns aL)
    (hgood : ∀ Q ∈ d.good, Q.card=m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) :
    CoeffBound (d.numerator t) (uniformBudget L m t q A) := by
  rw [CompleteThinProduct.complete_cyclic_numerator_scale d t ht columns aL aR
    hL hdelta hjL hjR hgood hgL hgR maps]
  have h := scale_bound ((4 : ℤ)^L) (d.matrixProductEntry aL aR)
    (C := 4^L) (by simp) (actual_matrix_product_bound d hX hY aL aR)
  apply h.mono
  calc
    4^L*(q*2^(2*m)*A^2) = q*2^(2*L+2*m)*A^2 := by
      rw [show (4 : ℕ)=2^2 by norm_num, ← pow_mul, pow_add]
      ring
    _ ≤ _ := quadratic_le_uniform L m t q A (2*L+2*m) (by omega)


/-- The Walsh summation loop has the same bound at every partial support. -/
 theorem partial_walsh_bound {q k A : ℕ} [NeZero q]
    (f : Cube k → Cyclic q) (hf : ∀ x, CoeffBound (f x) A)
    (a : Cube k) (support : Finset (Cube k)) :
    CoeffBound (∑ x ∈ support, character a x * f x) (2^k*A) := by
  intro j
  simp_rw [character_intCast, sum_coeff, intCast_mul_coeff]
  calc
    |∑ x ∈ support, character (R := ℤ) a x * f x j| ≤
        ∑ x ∈ support, |character (R := ℤ) a x * f x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ support, |f x j| := by simp only [abs_mul, character_abs, one_mul]
    _ ≤ ∑ _x ∈ support, (A : ℤ) := Finset.sum_le_sum (fun x _ => hf x j)
    _ = (support.card*A : ℕ) := by simp
    _ ≤ (2^k*A : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_right A (show support.card ≤ 2^k by simpa [Cube] using support.card_le_univ)

set_option maxHeartbeats 1000000 in
/-- Local dot-product accumulators, including all proper prefixes of
`finRange`, obey the same bound as the complete stored child. -/
 theorem contract_partial_accumulator_bound {q n A : ℕ} [NeZero q]
    (dims : Fin (n+1) → ℕ) (hdims : dims 0 ≤ 4)
    (normal : Bool) (row : Fin 6)
    (input : SharedEncoder.Dense (R := Polynomial (Cyclic q)) (n+1) dims)
    (hinput : ∀ a, PolynomialCoeffBound (SharedEncoder.read (n+1) dims input a) A)
    (rest : SharedEncoder.Coordinates (fun i => dims i.succ)) (support : Finset (Fin (dims 0))) :
    PolynomialCoeffBound (∑ a ∈ support, localPolynomial normal row
      ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩ *
      SharedEncoder.read (n+1) dims input (Fin.cons a rest)) (8*A) := by
  intro d k
  simp only [Polynomial.finsetSum_coeff, sum_coeff]
  calc
    |∑ a ∈ support, ((localPolynomial normal row
          ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩ *
          SharedEncoder.read (n+1) dims input (Fin.cons a rest)).coeff d) k| ≤
        ∑ a ∈ support, |((localPolynomial normal row
          ⟨a.val, lt_of_lt_of_le a.isLt hdims⟩ *
          SharedEncoder.read (n+1) dims input (Fin.cons a rest)).coeff d) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ support, (2*(A : ℤ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact localPolynomial_mul_bound normal row _ _ (hinput _) d k
    _ = (support.card : ℤ)*(2*(A : ℤ)) := by simp
    _ ≤ (8*A : ℕ) := by
      have hcard : support.card ≤ 4 := (support.card_le_univ.trans (by simpa using hdims))
      exact_mod_cast (show support.card*(2*A) ≤ 8*A by nlinarith)

/-- The five-child HIGH update's multiplication-free partial sums fit the
same global budget, even when only a proper subset has been accumulated. -/
 theorem actual_high_partial_accumulator_bound {q L m k t A : ℕ} [NeZero q]
    (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hgood : ∀ Q ∈ d.good, Q.card = m) (hk : k ≤ L)
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (run : ℤ) (stage : ℕ) (children : Fin 5 → HighBoxDP.States L m t)
    (support : Finset (Fin 5)) :
    CoeffBound (∑ a ∈ support, HighBoxDP.tableAfter
      (CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) stage (children a))
      (uniformBudget L m t q A) := by
  let leaf := CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
    CompleteThinProduct.sourceF CompleteThinProduct.sourceG
  have htable (a : Fin 5) := every_high_table_bound leaf
    (actual_global_leaf_bound d hgood hk hX hY run) stage (children a)
  have hsum := finite_sum_bound support (fun a => HighBoxDP.tableAfter leaf stage (children a))
    (5^(2*L)*(q*2^(14*L+2*m)*A^2)) (fun a _ => htable a)
  have hc : support.card ≤ 5 := by simpa using support.card_le_univ
  have hs := hsum.mono (Nat.mul_le_mul_right _ hc)
  have hb : 5*(5^(2*L)*(q*2^(14*L+2*m)*A^2)) ≤ uniformBudget L m t q A := by
    calc
      _ ≤ (2^3)*((2^3)^(2*L)*(q*2^(14*L+2*m)*A^2)) := by gcongr <;> norm_num
      _ = q*2^(20*L+2*m+3)*A^2 := by
        rw [← pow_mul, show 20*L+2*m+3=3+(3*(2*L)+(14*L+2*m)) by omega]
        simp only [pow_add]
        ring
      _ ≤ _ := quadratic_le_uniform L m t q A (20*L+2*m+3) (by omega)
  intro j
  simpa only [sum_coeff, leaf] using hs.mono hb j


/-- An arbitrary partial LOW loop, including any order of channel/degree
keys. This also bounds the accumulator before its final write. -/
noncomputable def cachedLowPartial {q m t : ℕ} [NeZero q]
    (support : Finset (Finset (Fin (2*m)) × Fin (t+1)))
    (left right : Finset (Fin (2*m)) → Polynomial (Cyclic q)) : Cyclic q :=
  ∑ key ∈ support, if key.1.card ≤ key.2.val then
    TensorContraction.residualWeight (2*m) t key.2.val *
      (left key.1*right key.1).coeff (key.2.val-key.1.card) else 0

set_option maxHeartbeats 1000000 in
 theorem cachedLow_partial_bound {q L m t A : ℕ} [NeZero q]
    (keys : Finset (Finset (Fin (2*m)))) (hkeys : keys.card ≤ 2^(2*m))
    (left right : Finset (Fin (2*m)) → Polynomial (Cyclic q))
    (hleft : ∀ C ∈ keys, PolynomialCoeffBound (left C) (2^(7*L+m)*A))
    (hright : ∀ C ∈ keys, PolynomialCoeffBound (right C) (2^(7*L+m)*A))
    (support : Finset (Finset (Fin (2*m)) × Fin (t+1)))
    (hsupport : ∀ key ∈ support, key.1 ∈ keys) :
    CoeffBound (cachedLowPartial support left right) (q*(t+1)^2*2^(14*L+6*m)*A^2) := by
  let term := fun key : Finset (Fin (2*m)) × Fin (t+1) =>
    if key.1.card ≤ key.2.val then
      TensorContraction.residualWeight (R := Cyclic q) (2*m) t key.2.val *
        (left key.1*right key.1).coeff (key.2.val-key.1.card) else 0
  have hterm (key : Finset (Fin (2*m)) × Fin (t+1)) (hk : key ∈ support) :
      CoeffBound (term key) (2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))) := by
    unfold term
    split_ifs
    · rw [residualWeight_intCast]
      have hp := polynomial_product_coefficient_bound (left key.1) (right key.1)
        (hleft key.1 (hsupport key hk)) (hright key.1 (hsupport key hk)) (key.2.val-key.1.card)
      have hdeg : key.2.val-key.1.card+1 ≤ t+1 := by have := key.2.isLt; omega
      have hb := scale_bound (a11Weight m t key.2.val)
        ((left key.1*right key.1).coeff (key.2.val-key.1.card))
        (a11Weight_bound m t key.2.val) (hp.mono (Nat.mul_le_mul_right _ hdeg))
      intro j
      simpa only [scale, intCast_mul_coeff] using hb j
    · intro j
      simp only [zero_coeff, abs_zero]
      positivity
  have hc : support.card ≤ 2^(2*m)*(t+1) := by
    calc
      support.card ≤ (keys.product (Finset.univ : Finset (Fin (t+1)))).card :=
        Finset.card_le_card (fun key hk => Finset.mem_product.mpr ⟨hsupport key hk, Finset.mem_univ _⟩)
      _ = keys.card*(t+1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hkeys
  have hs := (finite_sum_bound support term
    (2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))) hterm).mono
      (Nat.mul_le_mul_right _ hc)
  have he : (2^(2*m)*(t+1))*(2^(2*m)*((t+1)*(q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))) =
      q*(t+1)^2*2^(14*L+6*m)*A^2 := by
    rw [show 14*L+6*m=2*m+(2*m+((7*L+m)+(7*L+m))) by omega]
    simp only [pow_add]
    ring
  intro j
  simpa only [cachedLowPartial, sum_coeff, term, he] using hs j


/-- Any partial HIGH query read-sum, with the genuine handle-count cap,
is bounded directly from original input coefficients. -/
 theorem actual_high_read_sum_bound {q L m k t A : ℕ} [NeZero q]
    {ι : Type*} (d : CompleteThinProduct.SourceQueryData L m k (Cyclic q))
    (hgood : ∀ Q ∈ d.good, Q.card = m) (hk : k ≤ L)
    (hX : ∀ Q a b r s, CoeffBound (d.X Q a b r s) A)
    (hY : ∀ Q a r s b, CoeffBound (d.Y Q a r s b) A)
    (run : ℤ) (stage : ℕ) (handles : Finset ι) (hhandles : handles.card ≤ 2^(6*m))
    (address : ι → HighBoxDP.States L m t) :
    CoeffBound (∑ a ∈ handles, HighBoxDP.tableAfter
      (CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
        CompleteThinProduct.sourceF CompleteThinProduct.sourceG) stage (address a))
      (q*2^(20*L+8*m)*A^2) := by
  let leaf := CompleteThinProduct.globalLeaf (d.leftRun run) (d.rightRun run)
    CompleteThinProduct.sourceF CompleteThinProduct.sourceG
  have htable (a : ι) := every_high_table_bound leaf
    (actual_global_leaf_bound d hgood hk hX hY run) stage (address a)
  have hsum := finite_sum_bound handles (fun a => HighBoxDP.tableAfter leaf stage (address a))
    (5^(2*L)*(q*2^(14*L+2*m)*A^2)) (fun a _ => htable a)
  have hs := hsum.mono (Nat.mul_le_mul_right _ hhandles)
  have hb : 2^(6*m)*(5^(2*L)*(q*2^(14*L+2*m)*A^2)) ≤ q*2^(20*L+8*m)*A^2 := by
    calc
      _ ≤ 2^(6*m)*((2^3)^(2*L)*(q*2^(14*L+2*m)*A^2)) := by gcongr; norm_num
      _ = _ := by
        rw [← pow_mul, show 20*L+8*m=6*m+(3*(2*L)+(14*L+2*m)) by omega]
        simp only [pow_add]
        ring
  intro j
  simpa only [sum_coeff, leaf] using hs.mono hb j

end ThinMatrix.PipelineBitBounds

#print axioms ThinMatrix.PipelineBitBounds.rawLeftSource_bound
#print axioms ThinMatrix.PipelineBitBounds.rawRightSource_bound

#print axioms ThinMatrix.PipelineBitBounds.contract_stored_bound
#print axioms ThinMatrix.PipelineBitBounds.every_high_table_bound
#print axioms ThinMatrix.PipelineBitBounds.high_product_table_bound

#print axioms ThinMatrix.PipelineBitBounds.shared_run_stored_bound

#print axioms ThinMatrix.PipelineBitBounds.shared_run_uniform_bound
#print axioms ThinMatrix.PipelineBitBounds.every_cache_coefficient_bits
#print axioms ThinMatrix.PipelineBitBounds.every_high_coefficient_bits

#print axioms ThinMatrix.PipelineBitBounds.cachedLow_bound

#print axioms ThinMatrix.PipelineBitBounds.original_left_cache_bits
#print axioms ThinMatrix.PipelineBitBounds.original_right_cache_bits

#print axioms ThinMatrix.PipelineBitBounds.actual_global_leaf_bound
#print axioms ThinMatrix.PipelineBitBounds.actual_high_table_uniform_bound

#print axioms ThinMatrix.PipelineBitBounds.actual_high_coefficient_bits
#print axioms ThinMatrix.PipelineBitBounds.actual_matrix_product_bound
#print axioms ThinMatrix.PipelineBitBounds.actual_complete_numerator_bound

#print axioms ThinMatrix.PipelineBitBounds.partial_walsh_bound
#print axioms ThinMatrix.PipelineBitBounds.contract_partial_accumulator_bound
#print axioms ThinMatrix.PipelineBitBounds.actual_high_partial_accumulator_bound

#print axioms ThinMatrix.PipelineBitBounds.cachedLow_partial_bound

#print axioms ThinMatrix.PipelineBitBounds.actual_high_read_sum_bound
