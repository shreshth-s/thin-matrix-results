import CappedPrefixProgram

set_option autoImplicit false

/-! Physical window arrays to capped shared prefix encoding. The length and
cap are computed from retained dimensions/channel counts. Shape casts erase;
all actual grouping, prefix arithmetic and intermediate arrays are charged. -/
namespace ThinMatrix.WindowPrefixProgram
open BinaryCell BinaryGroupedCoordinates CroppedGroupedSuffix
open scoped BigOperators

def length (k ell : ℕ) : ℕ := min ell k
def prefixLength (k ell : ℕ) : ℕ := 2*k-length k ell

theorem dimension (k ell : ℕ) : prefixLength k ell+length k ell=2*k := by
  have := Nat.min_le_right ell k
  unfold prefixLength length
  omega

def castSource {N M C : ℕ} (h : N=M) (X : OppositeWindowLayer.Source N C) : OppositeWindowLayer.Source M C :=
  cast (congrArg (fun n => OppositeWindowLayer.Source n C) h) X

theorem castSource_value {N M C : ℕ} (h : N=M) (X : OppositeWindowLayer.Source N C) (w : Word M) (c : Fin C) :
    OppositeWindowLayer.value (castSource h X) w c=OppositeWindowLayer.value X (fun i => w (Fin.cast h i)) c := by
  cases h; rfl

theorem castSource_bound {N M C : ℕ} (h : N=M) (X : OppositeWindowLayer.Source N C)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) : OppositeWindowLayer.Bound (castSource h X) A := by
  cases h; exact ha

def reshape {k C : ℕ} (ell : ℕ) (X : OppositeWindowLayer.Source (2*k) C) :
    RetainedCappedGroups.Source (prefixLength k ell) (length k ell) C := castSource (dimension k ell).symm X

theorem suffix_count {k : ℕ} (ell : ℕ) (w : Word (prefixLength k ell+length k ell)) :
    (rare (fun j : Fin (length k ell) => w (Fin.natAdd (prefixLength k ell) j))).card=
      RetainedWindowPermutation.suffixRare k ell (fun i => w (Fin.cast (dimension k ell).symm i)) := by
  unfold rare RetainedWindowPermutation.suffixRare
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have he : Fin.natAdd (prefixLength k ell) j=Fin.cast (dimension k ell).symm
      (WindowSuffixPermutation.suffixIndex ((Nat.min_le_right ell k).trans (by omega)) j) := by
    apply Fin.ext
    simp [prefixLength,length,WindowSuffixPermutation.suffixIndex,Nat.add_comm]
  rw [he]

def cap (k ell total cn co : ℕ) : ℕ := (total-max cn co)*length k ell/k

structure Prepared (k ell C : ℕ) where
  rareCap : ℕ
  encoded : CappedPrefixProgram.Prepared (prefixLength k ell) (length k ell) rareCap C

def execute {k C : ℕ} (ell total cn co : ℕ) (X : OppositeWindowLayer.Source (2*k) C) :
    Run (Prepared k ell C) :=
  let r := cap k ell total cn co
  let out := CappedPrefixProgram.execute r (reshape ell X)
  ⟨⟨r,out.value⟩,out.bitSteps,out.control+32⟩

def bitBudget (k ell total cn co C A : ℕ) : ℕ :=
  CappedPrefixProgram.bitBudget (prefixLength k ell) (length k ell) (cap k ell total cn co) C A

def controlBudget (k ell total cn co C : ℕ) : ℕ :=
  CappedPrefixProgram.controlBudget (prefixLength k ell) (length k ell) (cap k ell total cn co) C+32

theorem execute_bits {k C : ℕ} (ell total cn co : ℕ) (X : OppositeWindowLayer.Source (2*k) C)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) : (execute ell total cn co X).bitSteps≤bitBudget k ell total cn co C A :=
  CappedPrefixProgram.execute_bits _ _ A (castSource_bound _ _ A ha)

theorem execute_control {k C : ℕ} (ell total cn co : ℕ) (X : OppositeWindowLayer.Source (2*k) C) :
    (execute ell total cn co X).control≤controlBudget k ell total cn co C :=
  Nat.add_le_add_right (CappedPrefixProgram.execute_control _ _) 32

/-- The full tensor on the actual window, with the crop discharged. -/
theorem query_exact {k C : ℕ} (ell total cn co : ℕ) (X : OppositeWindowLayer.Source (2*k) C)
    (hs : ∀ w c, cap k ell total cn co<RetainedWindowPermutation.suffixRare k ell w → OppositeWindowLayer.value X w c=0)
    (p : Fin (2^(length k ell))) (q : Fin (prefixLength k ell) → Fin 4)
    (active : Finset (Fin (length k ell))) (c : Fin C) :
    CappedPrefixProgram.query (execute ell total cn co X).value.encoded p q active c=
      EncoderCorrectness.tensorSum (fun _ : Fin (prefixLength k ell+length k ell) => 3)
        (Fin.append (fun i => BinaryPrefixContraction.form (q i))
          (fun i => localForm (((GroupedPreparation.pairKeys (length k ell)).get p).get i) (decide (i∈active))))
        (fun w => OppositeWindowLayer.value X (fun i => w (Fin.cast (dimension k ell).symm i)) c) := by
  change CappedPrefixProgram.query (CappedPrefixProgram.execute _ (reshape ell X)).value p q active c=_
  rw [CappedPrefixProgram.query_exact]
  · simp only [reshape,castSource_value]
  · intro w col h
    simp only [reshape,castSource_value]
    apply hs
    rwa [← suffix_count ell w]

#print axioms dimension
#print axioms castSource_value
#print axioms castSource_bound
#print axioms suffix_count
#print axioms execute_bits
#print axioms execute_control
#print axioms query_exact
end ThinMatrix.WindowPrefixProgram
