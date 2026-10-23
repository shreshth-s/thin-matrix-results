import CWIndependentCopies
import CWHashSeparation

set_option autoImplicit false

namespace ThinMatrix.CWHashedCandidates
open PolynomialDegeneration CWSixBlocks CWBlockWords CWIsolatedCandidates CWHashSeparation
variable {F : Type*} [Field F] [DecidableEq F]

def allowedX (n : ℕ) (b : F) (weights : PowerIndex F n) (B : Finset F) : Finset (Colors n) :=
  Finset.univ.filter (fun x => hx n b weights x ∈ B)
def allowedY (n : ℕ) (b w0 : F) (weights : PowerIndex F n) (B : Finset F) : Finset (Colors n) :=
  Finset.univ.filter (fun y => hy n b w0 weights y ∈ B)
def allowedZ (n : ℕ) (b w0 : F) (weights : PowerIndex F n) (B : Finset F) : Finset (Colors n) :=
  Finset.univ.filter (fun z => hz n b w0 weights z ∈ B)

def kept (n : ℕ) (reference : Word n) (b w0 : F) (weights : PowerIndex F n) (B : Finset F) : Finset (Word n) :=
  selected n reference (allowedX n b weights B) (allowedY n b w0 weights B) (allowedZ n b w0 weights B)

theorem candidate_same_bucket (h2 : (2:F)≠0) (n : ℕ) (reference w : Word n)
    (b w0 : F) (weights : PowerIndex F n) (B : Finset F) (hB : ThreeAPFree (B : Set F))
    (hw : w ∈ candidates n reference (allowedX n b weights B) (allowedY n b w0 weights B) (allowedZ n b w0 weights B)) :
    hx n b weights (wx n w)=hz n b w0 weights (wz n w) ∧
    hy n b w0 weights (wy n w)=hz n b w0 weights (wz n w) := by
  have h := (mem_candidates n reference w _ _ _).mp hw
  apply same_bucket h2 n b w0 weights (B : Set F) hB _ _ _ (word_compatible n w)
  · exact (Finset.mem_filter.mp h.2.1).2
  · exact (Finset.mem_filter.mp h.2.2.1).2
  · exact (Finset.mem_filter.mp h.2.2.2).2

theorem kept_same_bucket (h2 : (2:F)≠0) (n : ℕ) (reference w : Word n)
    (b w0 : F) (weights : PowerIndex F n) (B : Finset F) (hB : ThreeAPFree (B : Set F))
    (hw : w ∈ kept n reference b w0 weights B) :
    hx n b weights (wx n w)=hz n b w0 weights (wz n w) ∧
    hy n b w0 weights (wy n w)=hz n b w0 weights (wz n w) :=
  candidate_same_bucket h2 n reference w b w0 weights B hB (selected_subset _ _ _ _ _ hw)

theorem kept_card_lower_bound (n : ℕ) (reference : Word n) (b w0 : F)
    (weights : PowerIndex F n) (B : Finset F) :
    let E := candidates n reference (allowedX n b weights B) (allowedY n b w0 weights B) (allowedZ n b w0 weights B)
    E.card≤(kept n reference b w0 weights B).card+
      (FiniteCollisionCleanup.collisions E (wx n) (wy n) (wz n)).card :=
  retained_card _ _ _ _ _

#print axioms candidate_same_bucket
#print axioms kept_same_bucket
#print axioms kept_card_lower_bound
end ThinMatrix.CWHashedCandidates
