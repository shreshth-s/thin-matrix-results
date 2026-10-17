import ParameterMetadata
import BinaryAPSPHostTotalCosts
import BinaryTriangleExecution

/-!
# One concrete stored-bit APSP program

The parameter execution is bound once. Successful execution takes its runtime
block dimension and ascending prime list from the retained metadata, prepares
one concrete binary callback, and shares that callback through the complete
binary APSP host. The finite-size fallback is the direct binary scan.

Index transports below are erased equality casts. Integer views and the
reference callback occur only in refinement and correctness proofs. No
algorithmic branch calls the reference parameter program or sorts the pool.
-/
namespace ThinMatrix.BinaryAlignedAPSP
open BinaryAPSPCaller
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
attribute [local irreducible] ComputableParameters.block ComputableParameters.factorCount AlignedCertificate.S

def cap (n W : ℕ) : ℕ := 192*n*W+40

def castParameters {h h' U : ℕ} (he : h=h') (p : CompleteAPSP.Parameters h U) :
    CompleteAPSP.Parameters h' U := he ▸ p

theorem castParameters_pool {h h' U : ℕ} (he : h=h') (p : CompleteAPSP.Parameters h U) :
    (castParameters he p).pool=p.pool := by cases he; rfl

theorem castParameters_data {h h' U : ℕ} (he : h=h') (p : CompleteAPSP.Parameters h U) :
    (castParameters he p).pool=p.pool ∧ (castParameters he p).P=p.P ∧
      (castParameters he p).lam=p.lam ∧ (castParameters he p).k=p.k ∧
      (castParameters he p).M=p.M ∧ (castParameters he p).stages=p.stages := by
  cases he
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def castLabels {h h' U : ℕ} (he : h=h') (p : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ p.pool.card) : Vector ℕ (castParameters he p).pool.card := by
  cases he
  exact labels

theorem castLabels_spec {h h' U : ℕ} (he : h=h') (p : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ p.pool.card) (hl : labels=EndToEndAPSP.primeVector p.pool) :
    castLabels he p labels=EndToEndAPSP.primeVector (castParameters he p).pool := by
  cases he
  exact hl

theorem retained_block {n U : ℕ} (setup : ParameterExecution.Execution n U)
    (hsetup : setup=ParameterExecution.execute n U) :
    setup.metadata.block=ComputableParameters.block n := by
  rw [hsetup,ParameterExecution.execute_metadata]
  exact (ParameterExecution.decodeData_correct (ParameterExecution.prepare n U).value).1.trans
    (ParameterExecution.prepare_correct n U).1

abbrev SuccessPayload (n h : ℕ) :=
  BinaryTriangleExecution.CallbackPayload n h (BinaryTriangleExecution.HistoryPayload n h)

abbrev Payload (n : ℕ) :=
  Sum (BinaryTriangleExecution.DirectPayload n) (Sigma (SuccessPayload n))

def liftSuccess {n h : ℕ} (addressPrice : ℕ) (O : Oracle n (SuccessPayload n h)) : Oracle n (Payload n) :=
  fun A B T =>
    let output := O A B T
    { answers := output.answers
      payload := Sum.inr ⟨h,output.payload⟩
      work := output.work+4*(addressPrice+1)
      answerWrites := output.answerWrites }

def fallback (n addressPrice : ℕ) : Oracle n (Payload n) := fun A B T =>
  let output := BinaryTriangleExecution.directOracle n A B T
  { answers := output.answers
    payload := Sum.inl output.payload
    work := output.payload.bitSteps+(addressPrice+1)*output.payload.controlSites+4*(addressPrice+1)
    answerWrites := output.answerWrites }

structure SuccessfulSetup (n U h addressPrice : ℕ) where
  positive : 0<h
  parameters : CompleteAPSP.Parameters h U
  labels : Vector ℕ parameters.pool.card
  label_spec : labels=EndToEndAPSP.primeVector parameters.pool
  callback : BinaryTriangleExecution.PreparedOracle n h (BinaryTriangleExecution.HistoryPayload n h)
  callback_spec : callback=BinaryTriangleExecution.prepareConcreteFromPrimes positive parameters labels label_spec addressPrice

/-- Generic index transport keeps numerical parameter definitions out of the
kernel reduction needed to assemble a successful setup. -/
def makeSuccessful {n U oldh : ℕ} (h addressPrice : ℕ) (he : oldh=h) (hh : 0<h)
    (original : CompleteAPSP.Parameters oldh U) (originalLabels : Vector ℕ original.pool.card)
    (hlabels : originalLabels=EndToEndAPSP.primeVector original.pool) :
    SuccessfulSetup n U h addressPrice :=
  let parameters := castParameters he original
  let labels := castLabels he original originalLabels
  have hl : labels=EndToEndAPSP.primeVector parameters.pool := castLabels_spec he original originalLabels hlabels
  let callback := BinaryTriangleExecution.prepareConcreteFromPrimes hh parameters labels hl addressPrice
  ⟨hh,parameters,labels,hl,callback,rfl⟩


structure Preparation (n W addressPrice : ℕ) where
  setup : ParameterExecution.Execution n (cap n W)
  success : Option (Sigma (fun h => SuccessfulSetup n (cap n W) h addressPrice))
  oracle : Oracle n (Payload n)
  setupBits : ℕ
  setupControl : ℕ

/-- Public cap multiplication/addition are charged once, independently of
the graph coefficient serialization performed by the binary host. -/
def publicSetupBits (n W : ℕ) : ℕ := 1024*(n.size+W.size+10)^2

def prepareFromSetup {n : ℕ} (W addressPrice : ℕ)
    (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W)) : Preparation n W addressPrice :=
  match hp : setup.value with
  | none =>
    { setup := setup,success := none,oracle := fallback n addressPrice
      setupBits := setup.bitSteps+publicSetupBits n W,setupControl := 64 }
  | some original =>
    let h := setup.metadata.block
    have he : ComputableParameters.block n=h := (retained_block setup hsetup).symm
    have hh : 0<h := by rw [←he]; exact EndToEndAPSP.block_pos n
    let labels := ParameterMetadata.successfulLabels setup hsetup original hp
    let success := makeSuccessful h addressPrice he hh original labels
      (ParameterMetadata.successfulLabels_eq setup hsetup original hp)
    { setup := setup
      success := some ⟨h,success⟩
      oracle := liftSuccess addressPrice success.callback.oracle
      setupBits := setup.bitSteps+publicSetupBits n W+success.callback.setupBits
      setupControl := setup.metadata.pool.length+success.callback.setupControl+64 }

/-- There is one parameter execution, before the adaptive oracle lambda. -/
def prepare (n W addressPrice : ℕ) : Preparation n W addressPrice :=
  let setup := ParameterExecution.execute n (cap n W)
  prepareFromSetup W addressPrice setup rfl

def OracleCorrect {n : ℕ} (O : Oracle n (Payload n)) : Prop :=
  ∀ A B T i j, StoredMinPlusAPSP.decode (O A B T).answers i j=true ↔
    ∃ k, BinaryCell.view (StoredMinPlusAPSP.decode A i k)+
      BinaryCell.view (StoredMinPlusAPSP.decode B k j)+
      BinaryCell.view (StoredMinPlusAPSP.decode T i j)=0

theorem successful_correct {n U h addressPrice : ℕ} (success : SuccessfulSetup n U h addressPrice) :
    OracleCorrect (liftSuccess addressPrice success.callback.oracle) := by
  intro A B T i j
  simp only [liftSuccess]
  rw [success.callback_spec]
  exact BinaryTriangleExecution.prepareConcreteFromPrimes_correct success.positive success.parameters
    success.labels success.label_spec addressPrice A B T i j

theorem prepareFromSetup_correct {n : ℕ} (W addressPrice : ℕ)
    (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W)) :
    OracleCorrect (prepareFromSetup W addressPrice setup hsetup).oracle := by
  intro A B T i j
  unfold prepareFromSetup
  split
  · exact BinaryTriangleExecution.directOracle_correct n A B T i j
  · exact successful_correct _ A B T i j

theorem prepare_correct (n W addressPrice : ℕ) : OracleCorrect (prepare n W addressPrice).oracle :=
  prepareFromSetup_correct W addressPrice _ rfl

/-- The native oracle is a proof-only specification. It is not executed by
the stored-bit program. -/
theorem correct_refines_direct {n : ℕ} (O : Oracle n (Payload n)) (hO : OracleCorrect O) :
    BinaryAPSPCaller.Refines O (EndToEndAPSP.directCallback n) := by
  intro A B T
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  apply Bool.eq_iff_iff.mpr
  change StoredMinPlusAPSP.decode (O A B T).answers ⟨i,hi⟩ ⟨j,hj⟩=true ↔
    StoredMinPlusAPSP.decode (EndToEndAPSP.directCallback n
      (viewTable A) (viewTable B) (viewTable T)).answers ⟨i,hi⟩ ⟨j,hj⟩=true
  exact (hO A B T ⟨i,hi⟩ ⟨j,hj⟩).trans
    (by simpa only [viewTable_get] using (EndToEndAPSP.directCallback_correct n
      (viewTable A) (viewTable B) (viewTable T) ⟨i,hi⟩ ⟨j,hj⟩).symm)

structure Execution (n W addressPrice : ℕ) where
  preparation : Preparation n W addressPrice
  core : BinaryAPSPCaller.Execution n (Option Cell) (Payload n)
  work : ℕ

/-- Setup and all produced payloads/resources are retained from the same
execution. Returned callback work includes the payload-lifting overhead. -/
def run {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ) :
    Execution n W addressPrice :=
  let preparation := prepare n W addressPrice
  let core := BinaryAPSPCaller.run preparation.oracle w W
  ⟨preparation,core,preparation.setupBits+(addressPrice+1)*(preparation.setupControl+8)+
    core.hostBits+core.oracleWork+core.answerWrites⟩

theorem run_correct {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (viewOptional (run w W addressPrice).core.value)) :=
  BinaryAPSPCaller.run_correct (prepare n W addressPrice).oracle (EndToEndAPSP.directCallback n)
    (correct_refines_direct _ (prepare_correct n W addressPrice))
    (EndToEndAPSP.directCallback_correct n) w W hw hno

theorem run_work {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ) :
    (run w W addressPrice).work=(run w W addressPrice).preparation.setupBits+
      (addressPrice+1)*((run w W addressPrice).preparation.setupControl+8)+
      (run w W addressPrice).core.hostBits+(run w W addressPrice).core.oracleWork+
      (run w W addressPrice).core.answerWrites := rfl

theorem run_calls_faithful {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ) :
    ∀ c∈(run w W addressPrice).core.calls,c.Faithful (run w W addressPrice).preparation.oracle :=
  BinaryAPSPCaller.run_calls_faithful _ w W

theorem run_oracleWork {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ) :
    (run w W addressPrice).core.oracleWork=BinaryAPSPCaller.callWork (run w W addressPrice).core.calls :=
  BinaryAPSPCaller.run_oracleWork _ w W

theorem run_query_bound {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W addressPrice : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (c : BinaryAPSPCaller.Call n (Payload n)) (hc : c∈(run w W addressPrice).core.calls) :
    APSPAlgorithm.SymmetricQueryBound c.query ((64*n*W+13 : ℕ) : ℤ) :=
  BinaryAPSPCaller.run_query_bound (prepare n W addressPrice).oracle (EndToEndAPSP.directCallback n)
    (correct_refines_direct _ (prepare_correct n W addressPrice))
    (EndToEndAPSP.directCallback_correct n) w W hw c hc

#print axioms retained_block
#print axioms prepare_correct
#print axioms correct_refines_direct
#print axioms run_correct
#print axioms run_work
#print axioms run_calls_faithful
#print axioms run_oracleWork
#print axioms run_query_bound

end ThinMatrix.BinaryAlignedAPSP
