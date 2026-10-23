import DistinguishedResidualRoot
import ExactHalfCroppedEmbedding
import BinaryWindowPartition

set_option autoImplicit false

/-! Rare support of the genuine distinguished contraction. Layouts reindex
physical positions into distinguished and remaining coordinates. The finite
support proof works in every commutative ring, including the full cyclic
coefficient ring and the separate formal-polynomial ring; it does not infer
nonzero factors from an integral-domain hypothesis. -/
namespace ThinMatrix.DistinguishedResidualSupport
open WalshEmbedding DistinguishedResidualRoot
open scoped BigOperators
variable {R : Type*} [CommRing R]

abbrev Layout (L m k : ℕ) := Fin L ≃ Fin m ⊕ Fin k

def assemble {L m k : ℕ} {A : Type*} (e : Layout L m k) (a : Fin m → A) (b : Fin k → A) : Fin L → A :=
  fun i => Sum.elim a b (e i)

/-- A semantic layout for the actual set. Its finite enumeration is not an
executable or priced layout-construction algorithm. -/
noncomputable def layout {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m) : Layout L m (L-m) :=
  (Equiv.sumCompl (fun i => i∈Q)).symm.trans
    (Equiv.sumCongr (Q.equivFinOfCardEq hQ)
      (Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl,hQ])))

theorem layout_distinguished {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m) (i : Fin L) :
    (∃ j, layout Q hQ i=Sum.inl j) ↔ i∈Q := by
  by_cases hi : i∈Q <;> simp [layout,Equiv.sumCompl_symm_apply_of_pos,Equiv.sumCompl_symm_apply_of_neg,hi]

theorem ones_count {n : ℕ} (b : Cube n) : ones b=CyclicLightWindow.count b := by
  simp only [ones,CyclicLightWindow.count,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem ones_assemble {L m k : ℕ} (e : Layout L m k) (a : Cube m) (b : Cube k) :
    ones (assemble e a b)=ones a+ones b := by
  simp only [ones_count,CyclicLightWindow.count,assemble]
  rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_sum_type]
  rfl

def physicalChannels {L m k : ℕ} (e : Layout L m k) (channels : Cube m) : Finset (Fin L) :=
  Finset.univ.filter (fun i => assemble e channels (zeroBits k) i)

theorem physicalChannels_card {L m k : ℕ} (e : Layout L m k) (channels : Cube m) :
    (physicalChannels e channels).card=ones channels := by
  change ones (assemble e channels (zeroBits k))=ones channels
  rw [ones_assemble]
  simp [ones,zeroBits]

theorem physicalChannels_subset {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card=m) (channels : Cube m) :
    physicalChannels (layout Q hQ) channels ⊆ Q := by
  intro i hi
  have hb : assemble (layout Q hQ) channels (zeroBits (L-m)) i=true := (Finset.mem_filter.mp hi).2
  rcases he : layout Q hQ i with a | b
  · exact (layout_distinguished Q hQ i).mp ⟨a,he⟩
  · simp [assemble,he,zeroBits] at hb

def normalRemaining (a : Fin 3) : NormalLetter := ![.x1,.x2,.p2] a

def rareCount {k : ℕ} (w : CroppedGroupedSuffix.Word k) : ℕ := ones (fun i => decide (w i=2))

theorem normalRemaining_rare (a : Fin 3) : decide (normalRemaining a=.p2)=decide (a=2) := by
  fin_cases a <;> rfl

theorem oppositeRemaining_rare (a : Fin 3) :
    decide (SourceCoordinates.oppositeEquiv a=.w)=decide (a=2) := by fin_cases a <;> rfl

theorem normal_rare {L m k : ℕ} (e : Layout L m k) (n : Fin m → NormalLetter)
    (w : CroppedGroupedSuffix.Word k) :
    ones (normalP2Bits (assemble e n (fun i => normalRemaining (w i)))) = ones (normalP2Bits n)+rareCount w := by
  have he : normalP2Bits (assemble e n (fun i => normalRemaining (w i))) =
      assemble e (normalP2Bits n) (fun i => decide (w i=2)) := by
    funext i
    rcases h : e i with a | b <;> simp [normalP2Bits,assemble,h,normalRemaining_rare]
  rw [he,ones_assemble]
  rfl

theorem opposite_rare {L m k : ℕ} (e : Layout L m k) (channels : Cube m)
    (w : CroppedGroupedSuffix.Word k) :
    ones (oppositeWBits (assemble e (fun i => oppositeLetter (channels i))
      (fun i => SourceCoordinates.oppositeEquiv (w i)))) = ones channels+rareCount w := by
  have he : oppositeWBits (assemble e (fun i => oppositeLetter (channels i))
      (fun i => SourceCoordinates.oppositeEquiv (w i))) =
      assemble e channels (fun i => decide (w i=2)) := by
    funext i
    rcases h : e i with a | b
    · cases hc : channels a <;> simp [oppositeWBits,assemble,h,oppositeLetter,hc]
    · simp [oppositeWBits,assemble,h,oppositeRemaining_rare]
  rw [he,ones_assemble]
  rfl

def cropBoth {L : ℕ} (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : R :=
  if ones (normalP2Bits n)≤cap then CroppedSourceContraction.crop cap source n o else 0

theorem cropBoth_eq_crop {L : ℕ} (cap : ℕ)
    (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (h : ∀ n o, cap<ones (normalP2Bits n) → source n o=0) :
    cropBoth cap source=CroppedSourceContraction.crop cap source := by
  funext n o
  by_cases hn : ones (normalP2Bits n)≤cap
  · simp [cropBoth,hn]
  · simp [cropBoth,hn,CroppedSourceContraction.crop,h n o (by omega)]

/-- The opposite distinguished factors are singletons, contributing 2s or w.
The normal scalar contraction is H(z) or p2 at each distinguished position. -/
noncomputable def root {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) : R :=
  (∏ i, oppositeScale (R:=R) (co i))*contract cn z (fun n =>
    cropBoth cap source (assemble eN n (fun i => normalRemaining (wn i)))
      (assemble eO (fun i => oppositeLetter (co i)) (fun i => SourceCoordinates.oppositeEquiv (wo i))))

/-- Equality to the complete distinguished tensor sum, including all opposite
words. This is a scalar identity, not a claim that the dense sum is evaluated. -/
theorem root_eq_dense {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) :
    root eN eO cn co z cap source wn wo =
      ∑ n, ∑ o, kernel cn z n * (∏ i, oppositeFactor (co i) (o i)) *
        cropBoth cap source (assemble eN n (fun i => normalRemaining (wn i)))
          (assemble eO o (fun i => SourceCoordinates.oppositeEquiv (wo i))) := by
  simp_rw [mul_assoc,← Finset.mul_sum,opposite_contract]
  unfold root contract
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Sparse recursive evaluation of this same root. Only its inner normal
lookup count is bounded by evaluate_lookups; the outside scale and materialized
word/coefficient work still need execution and pricing. -/
theorem root_evaluate {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) :
    root eN eO cn co z cap source wn wo =
      (∏ i, oppositeScale (R:=R) (co i))*(evaluate m cn z (fun n =>
        cropBoth cap source (assemble eN n (fun i => normalRemaining (wn i)))
          (assemble eO (fun i => oppositeLetter (co i))
            (fun i => SourceCoordinates.oppositeEquiv (wo i))))).value := by
  rw [evaluate_value]
  rfl

theorem root_zero_normal {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) (h : cap<ones cn+rareCount wn) :
    root eN eO cn co z cap source wn wo=0 := by
  unfold root contract
  suffices hz : ∀ n, kernel cn z n * cropBoth cap source
      (assemble eN n (fun i => normalRemaining (wn i)))
      (assemble eO (fun i => oppositeLetter (co i)) (fun i => SourceCoordinates.oppositeEquiv (wo i)))=0 by
    simp [hz]
  intro n
  by_cases hn : kernel cn z n=0
  · simp [hn]
  · have hw := kernel_support cn z n hn
    have hb : ¬ ones (normalP2Bits (assemble eN n (fun i => normalRemaining (wn i))))≤cap := by
      rw [normal_rare,hw]; omega
    simp [cropBoth,hb]

theorem root_zero_opposite {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) (h : cap<ones co+rareCount wo) :
    root eN eO cn co z cap source wn wo=0 := by
  have hb : ¬ ones (oppositeWBits (assemble eO (fun i => oppositeLetter (co i))
      (fun i => SourceCoordinates.oppositeEquiv (wo i))))≤cap := by rw [opposite_rare]; omega
  simp [root,contract,cropBoth,CroppedSourceContraction.crop,hb]

theorem remaining_caps {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (wn wo : CroppedGroupedSuffix.Word k) (h : root eN eO cn co z cap source wn wo≠0) :
    ones cn+rareCount wn≤cap ∧ ones co+rareCount wo≤cap := by
  constructor
  · by_contra! hb; exact h (root_zero_normal eN eO cn co z cap source wn wo hb)
  · by_contra! hb; exact h (root_zero_opposite eN eO cn co z cap source wn wo hb)

#print axioms layout_distinguished
#print axioms ones_count
#print axioms ones_assemble
#print axioms physicalChannels_card
#print axioms physicalChannels_subset
#print axioms normalRemaining_rare
#print axioms oppositeRemaining_rare
#print axioms normal_rare
#print axioms opposite_rare
#print axioms cropBoth_eq_crop
#print axioms root_eq_dense
#print axioms root_evaluate
#print axioms root_zero_normal
#print axioms root_zero_opposite
#print axioms remaining_caps
end ThinMatrix.DistinguishedResidualSupport
