import GraphHalfSourceExecution
import HalfSourceDispatch
import HalfSourceAPSPHost

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

/-! Concrete exact-half controller backend. Valid factor histories execute
new-S dispatch and the shared LOW/HIGH producer. Exceptional histories retain
the existing exact binary fallback. This module closes correctness only;
its literal runtime still needs the separate aggregate cost theorem. -/
namespace ThinMatrix.GraphHalfSourceBackend
open BinaryTriangleExecution

structure PositivePayload (n h : ℕ) where
  factors : List ℕ
  dispatch : HalfSourceDispatch.Prepared n h factors
  produced : BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h)
    (GraphSelectedTable.Payload (GraphHalfSourceExecution.Execution dispatch.split.plan dispatch.plan.value) n h)
  metadataSites : ℕ

abbrev Payload (n h : ℕ) := Sum (HistoryPayload n h) (PositivePayload n h)

variable (scheme : RectangularBatch.Scheme) (hnum : scheme.num=861)
  (hden : scheme.den=500) (hz : scheme.z=15) (hvalid : scheme.Valid)

/-- Each public split and plan is computed once and retained in the payload. -/
def positiveTable {n h : ℕ} (A B T : IntTable n) (factors : List ℕ)
    (hv : EndToEndAPSP.ValidFactors factors) (metadataSites addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  let dispatch := HalfSourceDispatch.prepare n h factors hv
  let produced := GraphHalfSourceExecution.produce dispatch.split.plan dispatch.plan.value
    (HalfSourceDispatch.canonical n h factors hv).2.2 ⟨A,B,T⟩ scheme hnum hden hz hvalid addressPrice
  let metadata := metadataSites+dispatch.split.work+dispatch.plan.sites+32
  { counts := produced.counts
    payload := Sum.inr ⟨factors,dispatch,produced,metadata⟩
    work := produced.work+(addressPrice+1)*metadata }

theorem positive_modCount {n h : ℕ} (hh : 0<h) (A B T : IntTable n) (factors : List ℕ)
    (hv : EndToEndAPSP.ValidFactors factors) (metadataSites addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview
      ((positiveTable scheme hnum hden hz hvalid A B T factors hv metadataSites addressPrice).counts.get i)=
    (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount factors.prod i :=
  GraphHalfSourceExecution.modCount _ _ _ ⟨A,B,T⟩ scheme hnum hden hz hh hvalid addressPrice i

theorem positive_count_le {n h : ℕ} (A B T : IntTable n) (factors : List ℕ)
    (hv : EndToEndAPSP.ValidFactors factors) (metadataSites addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview
      ((positiveTable scheme hnum hden hz hvalid A B T factors hv metadataSites addressPrice).counts.get i)≤h :=
  GraphHalfSourceExecution.count_bound _ _ _ ⟨A,B,T⟩ scheme hnum hden hz hvalid addressPrice i

def concreteTable {n h : ℕ} (A B T : IntTable n) (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  let factors := selected++[candidate]
  let validation := FactorValidation.validate factors
  if hb : validation.1=true then
    positiveTable scheme hnum hden hz hvalid A B T factors
      ((FactorValidation.validate_correct factors).mp hb) (historySites selected+validation.2) addressPrice
  else
    let out := BinaryTriangleExecution.concreteTable A B T selected candidate active addressPrice
    { counts := out.counts,payload := Sum.inl out.payload
      work := out.work+(addressPrice+1)*(historySites selected+validation.2+16) }

theorem concreteTable_modCount {n h : ℕ} (hh : 0<h) (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview
      ((concreteTable scheme hnum hden hz hvalid A B T selected candidate active addressPrice).counts.get i)=
    (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount
      (selected.prod*candidate) i := by
  unfold concreteTable
  dsimp only
  split_ifs
  · simpa only [List.prod_append,List.prod_cons,List.prod_nil,Nat.mul_one] using
      positive_modCount scheme hnum hden hz hvalid hh A B T (selected++[candidate]) _ _ addressPrice i
  · exact BinaryTriangleExecution.concreteTable_modCount hh A B T selected candidate active addressPrice i

theorem concreteTable_count_le {n h : ℕ} (hh : 0<h) (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview
      ((concreteTable scheme hnum hden hz hvalid A B T selected candidate active addressPrice).counts.get i)≤h := by
  unfold concreteTable
  dsimp only
  split_ifs
  · exact positive_count_le scheme hnum hden hz hvalid A B T _ _ _ addressPrice i
  · exact BinaryTriangleExecution.concreteTable_count_le hh A B T selected candidate active addressPrice i

def concreteOracle {n h : ℕ} (A B T : IntTable n) (addressPrice : ℕ) :
    BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  ⟨fun selected candidate active=>concreteTable scheme hnum hden hz hvalid A B T selected candidate active addressPrice⟩

theorem concreteOracle_correct {n h : ℕ} (hh : 0<h) (A B T : IntTable n) (addressPrice : ℕ) :
    (concreteOracle scheme hnum hden hz hvalid (h:=h) A B T addressPrice).project.Correct
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)) := by
  intro selected candidate active i _hi
  simpa only [concreteOracle,BinaryControllerExecution.Oracle.project,
    BinaryControllerExecution.Table.project,CountedArrayComposite.Oracle.erase,
    BinaryControllerExecution.projectCounts,Vector.get_map] using
      concreteTable_modCount scheme hnum hden hz hvalid hh A B T selected candidate active addressPrice i

theorem concreteOracle_countsBound {n h : ℕ} (hh : 0<h) (A B T : IntTable n) (addressPrice : ℕ) :
    BinaryControllerExecution.OracleCountsBound
      (concreteOracle scheme hnum hden hz hvalid (h:=h) A B T addressPrice) h :=
  fun selected candidate active i=>concreteTable_count_le scheme hnum hden hz hvalid hh A B T selected candidate active addressPrice i

def concreteBackend (n h addressPrice : ℕ) (hh : 0<h) : Backend n h (Payload n h) :=
  ⟨(fun A B T=>concreteOracle scheme hnum hden hz hvalid A B T addressPrice),
    fun A B T=>concreteOracle_correct scheme hnum hden hz hvalid hh A B T addressPrice⟩

def factory : HalfSourceAPSPHost.BackendFactory :=
  ⟨Payload,fun n h price hh=>concreteBackend scheme hnum hden hz hvalid n h price hh⟩

theorem concreteTable_of_valid {n h : ℕ} (A B T : IntTable n) (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate])) :
    concreteTable scheme hnum hden hz hvalid A B T selected candidate active addressPrice=
      positiveTable scheme hnum hden hz hvalid A B T (selected++[candidate]) hv
        (historySites selected+(FactorValidation.validate (selected++[candidate])).2) addressPrice := by
  have hb := (FactorValidation.validate_correct (selected++[candidate])).mpr hv
  simp only [concreteTable,dif_pos hb]

theorem run_correct {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (BinaryAPSPCaller.viewOptional
        (HalfSourceAPSPHost.run (factory scheme hnum hden hz hvalid) w W addressPrice).core.value)) :=
  HalfSourceAPSPHost.run_correct (factory scheme hnum hden hz hvalid) w W addressPrice hw hno

#print axioms positive_modCount
#print axioms positive_count_le
#print axioms concreteTable_modCount
#print axioms concreteTable_count_le
#print axioms concreteOracle_correct
#print axioms concreteOracle_countsBound
#print axioms concreteTable_of_valid
#print axioms run_correct
end ThinMatrix.GraphHalfSourceBackend
