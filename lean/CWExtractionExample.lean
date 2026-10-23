import CWHashedCandidates

set_option autoImplicit false

/-! A bounded nonempty extraction using actual modular hashes and cleanup.
This witnesses two independent <16,16,16> copies in CW16 cubed; it is not
the entropy-scale copy bound for the requested rectangular aspect. -/
namespace ThinMatrix.CWExtractionExample
open PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts CWIsolatedCandidates CWHashedCandidates

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def reference : Word 3 := (.b011,(.b101,(.b110,PUnit.unit)))
def second : Word 3 := (.b110,(.b011,(.b101,PUnit.unit)))
def weights : PowerIndex (ZMod 7) 3 := (0,(1,(2,PUnit.unit)))
def bucketSet : Finset (ZMod 7) := {0,1,3}
def X := allowedX 3 (5:ZMod 7) weights bucketSet
def Y := allowedY 3 (5:ZMod 7) 1 weights bucketSet
def Z := allowedZ 3 (5:ZMod 7) 1 weights bucketSet

theorem bucket_free : ThreeAPFree (bucketSet : Set (ZMod 7)) := by decide
theorem two_nonzero : (2:ZMod 7)≠0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem selected_exact : selected 3 reference X Y Z={reference,second} := by
  have hinv : (2:ZMod 7)⁻¹=4 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  unfold selected
  have he : candidates 3 reference X Y Z={reference,second} := by
    ext w
    obtain ⟨a,b,c,u⟩ := w
    cases u
    simp only [mem_candidates, X, Y, Z, allowedX, allowedY, allowedZ,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    change (Marginals 3 (a,b,c,PUnit.unit) reference ∧
      CWHashSeparation.hx 3 5 weights (wx 3 (a,b,c,PUnit.unit)) ∈ bucketSet ∧
      CWHashSeparation.hy 3 5 1 weights (wy 3 (a,b,c,PUnit.unit)) ∈ bucketSet ∧
      CWHashSeparation.hz 3 5 1 weights (wz 3 (a,b,c,PUnit.unit)) ∈ bucketSet) ↔
      ((a,b,c,PUnit.unit) : Block×Block×Block×PUnit)=(.b011,.b101,.b110,PUnit.unit) ∨
      ((a,b,c,PUnit.unit) : Block×Block×Block×PUnit)=(.b110,.b011,.b101,PUnit.unit)
    cases a <;> cases b <;> cases c <;>
      simp [Marginals,count,wx,wy,wz,mapWord,cx,cy,cz,reference,Fin.forall_fin_succ] <;>
      norm_num [CWHashSeparation.hx,CWHashSeparation.hy,CWHashSeparation.hz,
        CWHashSeparation.weighted,CWHashSeparation.weightSum,weights,bucketSet,div_eq_mul_inv,hinv] <;> decide
  rw [he]
  decide

theorem selected_card : (selected 3 reference X Y Z).card=2 := by
  rw [selected_exact]
  decide

theorem dimensions (w : CWIndependentCopies.Copies 3 reference X Y Z) :
    Fintype.card (Rows 16 3 w.val)=16 ∧ Fintype.card (Inners 16 3 w.val)=16 ∧
    Fintype.card (Cols 16 3 w.val)=16 := by
  simpa [reference,count] using
    CWIndependentCopies.dimensions 3 reference X Y Z w

theorem exact_decomposition : FiniteTrilinear.total (CWIndependentCopies.terms 3 reference X Y Z)=
    CWIndependentCopies.directSum 3 reference X Y Z := CWIndependentCopies.exact_decomposition 3 reference X Y Z

#print axioms bucket_free
#print axioms two_nonzero
#print axioms selected_exact
#print axioms selected_card
#print axioms dimensions
#print axioms exact_decomposition
end ThinMatrix.CWExtractionExample
