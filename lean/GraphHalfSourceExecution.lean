import GraphHalfSourceSetup
import GraphHighBlockProduction
import GraphSelectedTable

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 2800000

/-! Complete optimized selected-coefficient production for one positive
physical factorization. The same execution supplies both values and costs:
shared source preparation, actual addressed LOW, scalar HIGH, full numerator
normalization, and controller incidence output are retained together. -/
namespace ThinMatrix.GraphHalfSourceExecution
open BinaryCell BinaryGroupedCoordinates SourceFormation
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev Rows := GraphOwnLowCollection.Rows (n:=n) (h:=h)
abbrev Low := RootProductCollection.Prepared (Rows (n:=n) (h:=h))
  (GraphOwnLowCollection.T f p) (M (n:=n)) (B (n:=n) (h:=h))

structure Execution where
  setup : Program (GraphHalfSourceSetup.Context f p)
  low : Run (Low f p)
  high : Program (Rows (n:=n) (h:=h))
  lowRows : Rows (n:=n) (h:=h)
  normalized : Run Cell × Run (GraphSelectedIncidences.Values (n:=n) (h:=h))
  work : ℕ

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)

/-- Mixed preparation charges are conservatively multiplied by the positive
indexed-control price. Binary LOW/normalization steps retain their own charge. -/
def execute (addressPrice : ℕ) : Execution f p :=
  let setup := GraphHalfSourceSetup.execute f p hm input
  let low := GraphOwnLowProduction.execute f p hm input scheme hnum hden hz setup.value.low
    (GraphHalfSourceSetup.low_correct f p hm input) setup.value.targets setup.value.keys.channels setup.value.weights
  let high := GraphHighBlockProduction.execute f p setup.value.shape (fun b => setup.value.high.get b)
    setup.value.targets.requests (GraphHalfSourceSetup.requests_bound f p hm input)
  let lowRows := Vector.ofFn (RootProductCollection.output low.value)
  let normalized := BinaryLowHighNormalize.table p.L lowRows high.value
  ⟨setup,low,high,lowRows,normalized,
    (addressPrice+1)*setup.operations+low.bitSteps+(addressPrice+1)*low.control+
    (addressPrice+1)*high.operations+(addressPrice+1)*(16*M (n:=n)+32)+
    normalized.1.bitSteps+normalized.2.bitSteps+
    (addressPrice+1)*(normalized.1.control+normalized.2.control+16)⟩

attribute [local irreducible] GraphAdaptiveBatchSources.Correct GraphPrefixProgram.fromInputs

theorem low_value (hv : scheme.Valid) (addressPrice : ℕ)
    (j : Fin (M (n:=n))) (b : Fin (B (n:=n) (h:=h))) :
    view (((execute f p hm input scheme hnum hden hz addressPrice).lowRows.get j).get b)=
      GraphSelectedNormalize.lowValue f p input j b := by
  simp only [execute,Vector.get_ofFn]
  exact GraphOwnLowProduction.correct f p hm input (GraphHalfSourceSetup.bands_bound f p input.target)
    scheme hnum hden hz (GraphHalfSourceSetup.execute f p hm input).value.low
    (GraphHalfSourceSetup.low_correct f p hm input) hv _ (GraphHalfSourceSetup.channels_eq f p hm input)
    _ (GraphHalfSourceSetup.weights_eq f p hm input) j b

theorem high_value (addressPrice : ℕ)
    (j : Fin (M (n:=n))) (b : Fin (B (n:=n) (h:=h))) :
    view (((execute f p hm input scheme hnum hden hz addressPrice).high.value.get j).get b)=
      GraphSelectedNormalize.highValue f p input j b := by
  exact GraphHighBlockProduction.correct f p _ _ _ (GraphHalfSourceSetup.requests_bound f p hm input)
    input (GraphHalfSourceSetup.high_correct f p hm input) (GraphHalfSourceSetup.shape_eq f p hm input)
    (GraphHalfSourceSetup.requests_eq f p hm input) j b

theorem correct (hv : scheme.Valid) (addressPrice : ℕ)
    (j : Fin (M (n:=n))) (b : Fin (B (n:=n) (h:=h))) :
    view (BinaryLowHighNormalize.output
      (execute f p hm input scheme hnum hden hz addressPrice).normalized.2.value j b)=
      FoldedRequestBounds.count f b input j :=
  GraphSelectedNormalize.correct f p input _ _
    (low_value f p hm input scheme hnum hden hz hv addressPrice)
    (high_value f p hm input scheme hnum hden hz addressPrice) j b

/-- Final wrapping consumes this execution's stored values and literal work. -/
def produce (hv : scheme.Valid) (addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h)
      (GraphSelectedTable.Payload (Execution f p) n h) :=
  let out := execute f p hm input scheme hnum hden hz addressPrice
  GraphSelectedTable.execute f input out.normalized.2.value
    (correct f p hm input scheme hnum hden hz hv addressPrice) out out.work addressPrice

theorem modCount (hh : 0<h) (hv : scheme.Valid) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((produce f p hm input scheme hnum hden hz hv addressPrice).counts.get i)=
      (EndToEndAPSP.flatInstance (h:=h) (BinaryFoldedFormation.viewTable input.left)
        (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target)).modCount r i :=
  GraphSelectedTable.correct f input _ (correct f p hm input scheme hnum hden hz hv addressPrice) hh _ _ _ i

theorem count_bound (hv : scheme.Valid) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((produce f p hm input scheme hnum hden hz hv addressPrice).counts.get i)≤h :=
  GraphSelectedTable.count_bound f input _ (correct f p hm input scheme hnum hden hz hv addressPrice) _ _ _ i

theorem produce_work (hv : scheme.Valid) (addressPrice : ℕ) :
    (produce f p hm input scheme hnum hden hz hv addressPrice).work≤
      (execute f p hm input scheme hnum hden hz addressPrice).work+
      EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
      (addressPrice+1)*(EndToEndAPSP.incidenceSize n h*
        (64*(EndToEndAPSP.incidenceSize n h).size^2+54)+21) :=
  GraphSelectedTable.work f input _ (correct f p hm input scheme hnum hden hz hv addressPrice) _ _ _

#print axioms low_value
#print axioms high_value
#print axioms correct
#print axioms modCount
#print axioms count_bound
#print axioms produce_work
end ThinMatrix.GraphHalfSourceExecution
