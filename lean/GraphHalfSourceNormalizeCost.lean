import GraphHalfSourceExecution

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-! Actual full-numerator normalization and final output costs. Magnitudes
come from the proved semantic LOW/HIGH values, independently of the fast
completion implementation. Division is only after the two sums are joined. -/
namespace ThinMatrix.GraphHalfSourceNormalizeCost
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

noncomputable def lowMagnitude : ℕ := GraphNormalizedBand.lowMagnitude p.L p.m p.t f.cyclic
noncomputable def highMagnitude : ℕ := GraphNormalizedBand.highMagnitude p.L p.m p.t f.cyclic

attribute [local irreducible] GraphPrefixProgram.fromInputs

theorem low_bound (input : BinaryFoldedFormation.Inputs n)
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (b : Fin (CompactBlocks.blockCount n h)) :
    (GraphSelectedNormalize.lowValue f p input j b).natAbs≤lowMagnitude f p :=
  GraphLowMaskAssembly.execute_bound f p b input
    (GraphOwnRootSpec.physical f p input.target j).bandL
    (GraphOwnRootSpec.physical f p input.target j).bandR 0 j
    (GraphOwnRootSpec.physical f p input.target j).coefficient

theorem high_bound (input : BinaryFoldedFormation.Inputs n)
    (j : Fin (FoldedBackendExecution.windowQuerySize n)) (b : Fin (CompactBlocks.blockCount n h)) :
    (GraphSelectedNormalize.highValue f p input j b).natAbs≤highMagnitude f p :=
  GraphHighFamily.fromInputs_bound f p b input
    (GraphOwnRootSpec.physical f p input.target j).bandL
    (GraphOwnRootSpec.physical f p input.target j).bandR 0 j
    (GraphOwnRootSpec.physical f p input.target j).coefficient

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)

noncomputable def bitsBudget : ℕ :=
  p.L*BackendScalarBits.backendScalarUnit (2*p.L+3)+
    FoldedBackendExecution.windowQuerySize n*(CompactBlocks.blockCount n h*
      BinaryLowHighNormalize.cellBudget p.L (lowMagnitude f p) (highMagnitude f p))

def controlBudget : ℕ :=
  8*p.L+1+FoldedBackendExecution.windowQuerySize n*(44*CompactBlocks.blockCount n h+40)+8

theorem bits (hv : scheme.Valid) (addressPrice : ℕ) :
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).normalized.1.bitSteps+
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).normalized.2.bitSteps≤bitsBudget f p := by
  apply BinaryLowHighNormalize.table_bits
  · intro j b
    change (view (((GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).lowRows.get j).get b)).natAbs≤_
    rw [GraphHalfSourceExecution.low_value f p hm input scheme hnum hden hz hv addressPrice j b]
    exact low_bound f p input j b
  · intro j b
    change (view (((GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).high.value.get j).get b)).natAbs≤_
    rw [GraphHalfSourceExecution.high_value f p hm input scheme hnum hden hz addressPrice j b]
    exact high_bound f p input j b

theorem control (addressPrice : ℕ) :
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).normalized.1.control+
    (GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice).normalized.2.control≤controlBudget f p :=
  BinaryLowHighNormalize.table_control _ _ _

/-- No assumed backend work: only the literal source, LOW and HIGH child
counters remain, plus fully proved normalization and incidence costs. -/
theorem produce_work (hv : scheme.Valid) (addressPrice : ℕ) :
    let out := GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice
    (GraphHalfSourceExecution.produce f p hm input scheme hnum hden hz hv addressPrice).work≤
      (addressPrice+1)*out.setup.operations+out.low.bitSteps+(addressPrice+1)*out.low.control+
      (addressPrice+1)*out.high.operations+bitsBudget f p+
      EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
      (addressPrice+1)*(16*FoldedBackendExecution.windowQuerySize n+48+controlBudget f p+
        EndToEndAPSP.incidenceSize n h*(64*(EndToEndAPSP.incidenceSize n h).size^2+54)+21) := by
  dsimp only
  have hp := GraphHalfSourceExecution.produce_work f p hm input scheme hnum hden hz hv addressPrice
  have hb := bits f p hm input scheme hnum hden hz hv addressPrice
  have hc := control f p hm input scheme hnum hden hz addressPrice
  let out := GraphHalfSourceExecution.execute f p hm input scheme hnum hden hz addressPrice
  have he : out.work=(addressPrice+1)*out.setup.operations+out.low.bitSteps+(addressPrice+1)*out.low.control+
      (addressPrice+1)*out.high.operations+(addressPrice+1)*(16*FoldedBackendExecution.windowQuerySize n+32)+
      out.normalized.1.bitSteps+out.normalized.2.bitSteps+
      (addressPrice+1)*(out.normalized.1.control+out.normalized.2.control+16) := rfl
  change _≤out.work+_+_ at hp
  rw [he] at hp
  change out.normalized.1.bitSteps+out.normalized.2.bitSteps≤_ at hb
  change out.normalized.1.control+out.normalized.2.control≤_ at hc
  change _≤(addressPrice+1)*out.setup.operations+out.low.bitSteps+(addressPrice+1)*out.low.control+
      (addressPrice+1)*out.high.operations+bitsBudget f p+_+_
  nlinarith only [hp,hb,Nat.mul_le_mul_left (addressPrice+1) hc]

#print axioms low_bound
#print axioms high_bound
#print axioms bits
#print axioms control
#print axioms produce_work
end ThinMatrix.GraphHalfSourceNormalizeCost
