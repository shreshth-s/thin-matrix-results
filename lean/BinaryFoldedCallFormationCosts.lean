import BinaryFoldedMetadataBounds

/-!
# Source formation on already stored binary callback inputs

This lemma consumes the same binary tables passed by the adaptive caller.
There is no serialization through their integer views. Public metadata bounds
are discharged by computed phase geometry; only the original stored input's
explicit magnitude-width bound is required by the local interface.
-/

namespace ThinMatrix.BinaryFoldedCallFormationCosts
open BinaryFoldedFormation BinaryFoldedFormationCost BinaryFoldedMetadataBounds
open FoldedBackendExecution
noncomputable section

def formationFactor (degree : ℕ) : ℕ :=
  6000000000000*(degree+metadataConstant+11)^3

theorem computed_formation_cost {n r degree : ℕ} (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n)
    (f : CompactBlocks.PhysicalFactorization r)
    (hfold : f.folded=call.folded AlignedCertificate.S)
    (hcyclic : f.cyclic=call.cyclic AlignedCertificate.S)
    (b : Fin (CompactBlocks.blockCount n (ComputableParameters.block n)))
    (input : Inputs n)
    (hl : TableBound (degree*n.size+1) input.left)
    (hr : TableBound (degree*n.size+1) input.right) :
    (formSources f b input).bitSteps ≤ formationFactor degree*(n.size+1)^3*
      (f.cyclic*outerSize n (physicalFold f)*
        middleSize (ComputableParameters.block n) (physicalFold f)) := by
  have hm := computed_metadata hn call f hfold hcyclic b
  have hc := formSources_cost f b input hm.1 hl hr (by omega)
    (Nat.pos_of_ne_zero (NeZero.ne _)) f.cyclic_pos hm.2
  have hw : degree*n.size+1+metadataWidth n+10 ≤
      (degree+metadataConstant+11)*(n.size+1) := by
    simp only [metadataWidth,Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega
  calc
    _ ≤ 3000000000000*(degree*n.size+1+metadataWidth n+10)^3*
        (2*f.cyclic*outerSize n (physicalFold f)*
          middleSize (ComputableParameters.block n) (physicalFold f)) := hc
    _ ≤ 3000000000000*((degree+metadataConstant+11)*(n.size+1))^3*
        (2*f.cyclic*outerSize n (physicalFold f)*
          middleSize (ComputableParameters.block n) (physicalFold f)) := by gcongr
    _ = _ := by unfold formationFactor;ring

#print axioms computed_formation_cost

end
end ThinMatrix.BinaryFoldedCallFormationCosts
