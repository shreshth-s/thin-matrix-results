import GraphSelectedHigh
import HalfSourceHighCounters

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphHighPreparation
open ExactHalfSourcePlan RetainedHighSources SourceFormation
variable {n h r K : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev Tables (_L m q K : ℕ) := Vector (Vector (Vector (Vector (Vector
  (BinaryHighTable.Table q) (2*m+1)) (J m)) (J m)) K) K

/-- Build all pair boxes from retained HIGH encoders. There is no encoder in
this loop, including its translation and degree-run loops. -/
def tables (stored : Vector (Encoded p.L p.m f.cyclic) K) (size : ℕ) : Program (Tables p.L p.m f.cyclic K) :=
  vectorBuild K fun a => vectorBuild K fun b =>
    vectorBuild (J p.m) fun u => vectorBuild (J p.m) fun v =>
      vectorBuild (2*p.m+1) fun run =>
        let out := GraphRetainedHigh.boxes f p stored size a b u v run
        ⟨out.value,out.work+8⟩

theorem tables_get (stored : Vector (Encoded p.L p.m f.cyclic) K) (size : ℕ)
    (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((((tables f p stored size).value.get a).get b).get u).get v).get run)=
      (GraphRetainedHigh.boxes f p stored size a b u v run).value := by
  simp only [tables,vectorBuild_get]

noncomputable def tablesBudget (L m t q K A : ℕ) :=
  (((((BinaryHighTable.preparationBudget L m t q (BinaryCroppedHighBoxes.magnitude L A)+16)*(2*m+1)+8)*J m+8)*J m+8)*K+8)*K

variable (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
  (ids : Vector ℕ K) (sources : GraphRetainedHigh.Sources f p (K:=K))
  (hc : GraphRetainedHigh.Correct f p block input ids sources)
include hc

 theorem tables_work :
    (tables f p (bank p.t (p.m/2) sources).value (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value).operations ≤
      tablesBudget p.L p.m p.t f.cyclic K (2^(p.L+p.m)) := by
  have hr (a b : Fin K) (u v : Fin (J p.m)) := vectorBuild_cost (2*p.m+1)
    (BinaryHighTable.preparationBudget p.L p.m p.t f.cyclic (BinaryCroppedHighBoxes.magnitude p.L (2^(p.L+p.m)))+8)
    (fun run => let out := GraphRetainedHigh.boxes f p (bank p.t (p.m/2) sources).value (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run
      (⟨out.value,out.work+8⟩ : Program (BinaryHighTable.Table f.cyclic)))
    (fun run => Nat.add_le_add_right (GraphRetainedHigh.boxes_work f p block input ids sources hc a b u v run) 8)
  have hv (a b : Fin K) (u : Fin (J p.m)) := vectorBuild_cost (J p.m) _ _ (hr a b u)
  have hu (a b : Fin K) := vectorBuild_cost (J p.m) _ _ (hv a b)
  have hb (a : Fin K) := vectorBuild_cost K _ _ (hu a)
  have ha := vectorBuild_cost K _ _ hb
  exact ha.trans_eq (by unfold tablesBudget; ring)

/-- Shared HIGH preparation consumes diagonal source stores already retained
by the source pipeline. Size construction and both encoders run once. -/
def execute (sources : GraphRetainedHigh.Sources f p (K:=K)) :
    Program (Vector (Encoded p.L p.m f.cyclic) K × Tables p.L p.m f.cyclic K) :=
  let stored := bank p.t (p.m/2) sources
  let size := BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))
  let out := tables f p stored.value size.value
  ⟨(stored.value,out.value),stored.operations+size.bitSteps+out.operations+8⟩

noncomputable def budget (L m t q K : ℕ) : ℕ :=
  K*(2*sideBudget L m t q (m/2) (2^(L+m))+16)+
    BinaryCroppedHighBoxes.setupBudget L (2^(L+m))+
      tablesBudget L m t q K (2^(L+m))+8

 theorem execute_work : (execute f p sources).operations ≤ budget p.L p.m p.t f.cyclic K := by
  have hs := GraphRetainedHigh.bank_work f p block input ids sources hc
  have ht := tables_work f p block input ids sources hc
  have hp := BinaryCroppedHighBoxes.setup_price p.L (2^(p.L+p.m))
  dsimp only [execute]
  unfold budget
  omega

 theorem execute_get (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((((execute f p sources).value.2.get a).get b).get u).get v).get run)=
      (BinaryCroppedHighBoxes.execute p.L p.m p.t f.cyclic (p.m/2) (2^(p.L+p.m))
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value false u v run)
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value true u v run)).boxes := by
  unfold execute
  rw [tables_get]
  exact GraphRetainedHigh.boxes_match f p block input ids sources hc a b u v run

#print axioms tables_get
#print axioms tables_work
#print axioms execute_work
#print axioms execute_get
end ThinMatrix.GraphHighPreparation
