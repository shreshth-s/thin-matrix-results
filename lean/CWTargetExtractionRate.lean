import CWEntropyFloors

set_option autoImplicit false
namespace ThinMatrix.CWTargetExtractionRate
open Filter
open scoped Topology
open PolynomialDegeneration CWSixBlocks CWBlockWords CWCanonicalType CWTargetMarginals CWTypePrimeChoice
open CWHashedCandidates CWEntropySurvival

abbrev Sample (s : ℕ) := CWHashFibers.Sample (ZMod (selected (size s) (reference s))) (size s)
def buckets (s : ℕ) := ModularBehrendBuckets.buckets (selected (size s) (reference s))
def X (s : ℕ) (r : Sample s) := allowedX (size s) r.1 r.2.2 (buckets s)
def Y (s : ℕ) (r : Sample s) := allowedY (size s) r.1 r.2.1 r.2.2 (buckets s)
def Z (s : ℕ) (r : Sample s) := allowedZ (size s) r.1 r.2.1 r.2.2 (buckets s)
abbrev Copies (s : ℕ) (r : Sample s) :=
  CWIndependentCopies.Copies (size s) (reference s) (X s r) (Y s r) (Z s r)

theorem copy_card (s : ℕ) (r : Sample s) : Fintype.card (Copies s r)=
    (CWQuantitativeCleanup.survivors (selected (size s) (reference s))
      (size s) (reference s) (buckets s) r).card := Fintype.card_coe _

theorem dimensions (s : ℕ) (r : Sample s) (w : Copies s r) :
    Fintype.card (Rows 16 (size s) w.val)=16^(s*4000000000000) ∧
    Fintype.card (Inners 16 (size s) w.val)=16^(s*60000000000000) ∧
    Fintype.card (Cols 16 (size s) w.val)=16^(s*6888000000000) :=
  extracted_dimensions s (X s r) (Y s r) (Z s r) w

/-- A finite-base extraction contract: actual hash-filtered coordinates,
independent matrix tensors of the target aspect, and the exact rational
separated decomposition. No asymptotic-sum or execution-cost premise. -/
theorem exponential_extraction (ε : ℝ) (he : 0<ε) :
    ∀ᶠ s : ℕ in atTop, ∃ r : Sample s,
      Real.exp ((size s:ℝ)*(rate-ε)) ≤ Fintype.card (Copies s r) ∧
      Fintype.card (CWInterpolationProgram.Request (size s))=(10*size s+1)*18^(size s) ∧
      (∀ w : Copies s r,
        Fintype.card (Rows 16 (size s) w.val)=16^(s*4000000000000) ∧
        Fintype.card (Inners 16 (size s) w.val)=16^(s*60000000000000) ∧
        Fintype.card (Cols 16 (size s) w.val)=16^(s*6888000000000)) ∧
      FiniteTrilinear.total (CWIndependentCopies.terms (size s) (reference s) (X s r) (Y s r) (Z s r))=
        CWIndependentCopies.directSum (size s) (reference s) (X s r) (Y s r) (Z s r) := by
  filter_upwards [CWEntropySurvival.exponential_survival ε he] with s hs
  obtain ⟨r,hr⟩ := hs
  refine ⟨r,?_,CWIndependentCopies.term_count (size s),dimensions s r,
    CWIndependentCopies.exact_decomposition _ _ _ _ _⟩
  simpa only [copy_card,buckets] using hr

/-- A fixed slack admits a positive finite integral base. This existential
statement does not supply or price a recursive multiplication algorithm. -/
theorem exists_positive_base (ε : ℝ) (he : 0<ε) :
    ∃ s : ℕ,0<s ∧ ∃ r : Sample s,
      Real.exp ((size s:ℝ)*(rate-ε)) ≤ Fintype.card (Copies s r) := by
  obtain ⟨s,hs,h⟩ := ((exponential_extraction ε he).and (eventually_ge_atTop 1)).exists
  obtain ⟨r,hr,_,_,_⟩ := hs
  exact ⟨s,by omega,r,hr⟩

#print axioms copy_card
#print axioms dimensions
#print axioms exponential_extraction
#print axioms exists_positive_base
end ThinMatrix.CWTargetExtractionRate
