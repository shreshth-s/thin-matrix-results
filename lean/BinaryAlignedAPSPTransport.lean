import BinaryAlignedAPSP

/-!
# Resource transport across the retained runtime block index

All transport lemmas are generic in the two natural indices. They avoid
unfolding the numerical block selector when an actual prepared callback is
compared with the same callback at its original parameter index. These are
equalities of returned resources, without a fast-cost premise.
-/
namespace ThinMatrix.BinaryAlignedAPSPTransport
open BinaryAPSPCaller BinaryAlignedAPSP
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
attribute [local irreducible] ComputableParameters.block ComputableParameters.factorCount AlignedCertificate.S

def oldPositive {oldh h : ℕ} (he : oldh=h) (hh : 0<h) : 0<oldh := he.symm ▸ hh

theorem callback_setupBits {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) :
    (makeSuccessful (n:=n) h a he hh p labels hl).callback.setupBits=
      (BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).setupBits := by
  cases he
  rfl

theorem callback_setupControl {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) :
    (makeSuccessful (n:=n) h a he hh p labels hl).callback.setupControl=
      (BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).setupControl := by
  cases he
  rfl

theorem callback_work {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) (A B T : IntTable n) :
    ((makeSuccessful (n:=n) h a he hh p labels hl).callback.oracle A B T).work=
      ((BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).oracle A B T).work := by
  cases he
  rfl

theorem callback_answerWrites {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) (A B T : IntTable n) :
    ((makeSuccessful (n:=n) h a he hh p labels hl).callback.oracle A B T).answerWrites=
      ((BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).oracle A B T).answerWrites := by
  cases he
  rfl

theorem lifted_work {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) (A B T : IntTable n) :
    (liftSuccess a (makeSuccessful (n:=n) h a he hh p labels hl).callback.oracle A B T).work=
      ((BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).oracle A B T).work+
        4*(a+1) := by
  cases he
  rfl

theorem lifted_answerWrites {n U oldh h : ℕ} (a : ℕ) (he : oldh=h) (hh : 0<h)
    (p : CompleteAPSP.Parameters oldh U) (labels : Vector ℕ p.pool.card)
    (hl : labels=EndToEndAPSP.primeVector p.pool) (A B T : IntTable n) :
    (liftSuccess a (makeSuccessful (n:=n) h a he hh p labels hl).callback.oracle A B T).answerWrites=
      ((BinaryTriangleExecution.prepareConcreteFromPrimes (n:=n) (oldPositive he hh) p labels hl a).oracle A B T).answerWrites := by
  cases he
  rfl

/-- A value specification of the exact record retained in the successful
branch. This helper is not called by the actual APSP entry point. -/
def successRecord {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) : SuccessfulSetup n (cap n W) setup.metadata.block a :=
  let h := setup.metadata.block
  have he : ComputableParameters.block n=h := (retained_block setup hsetup).symm
  have hh : 0<h := by rw [←he]; exact EndToEndAPSP.block_pos n
  let labels := ParameterMetadata.successfulLabels setup hsetup p hp
  makeSuccessful (n:=n) h a he hh p labels (ParameterMetadata.successfulLabels_eq setup hsetup p hp)

theorem prepareFromSetup_of_some {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    prepareFromSetup W a setup hsetup=
      let success := successRecord W a setup hsetup p hp
      { setup := setup
        success := some ⟨setup.metadata.block,success⟩
        oracle := liftSuccess a success.callback.oracle
        setupBits := setup.bitSteps+publicSetupBits n W+success.callback.setupBits
        setupControl := setup.metadata.pool.length+success.callback.setupControl+64 } := by
  unfold prepareFromSetup
  split
  · rename_i hnone
    rw [hp] at hnone
    contradiction
  · rename_i original horiginal
    have he : original=p := Option.some.inj (horiginal.symm.trans hp)
    cases he
    rfl

theorem prepared_success_value {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).success=
      some ⟨setup.metadata.block,successRecord W a setup hsetup p hp⟩ := by
  rw [prepareFromSetup_of_some W a setup hsetup p hp]

theorem prepared_oracle {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).oracle=
      liftSuccess a (successRecord W a setup hsetup p hp).callback.oracle := by
  rw [prepareFromSetup_of_some W a setup hsetup p hp]

theorem prepared_setupBits {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).setupBits=
      setup.bitSteps+publicSetupBits n W+(successRecord W a setup hsetup p hp).callback.setupBits := by
  rw [prepareFromSetup_of_some W a setup hsetup p hp]

theorem prepared_setupControl {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).setupControl=
      setup.metadata.pool.length+(successRecord W a setup hsetup p hp).callback.setupControl+64 := by
  rw [prepareFromSetup_of_some W a setup hsetup p hp]

/-- Original-index specification of the same retained callback. The concrete
APSP entry point does not execute this helper. -/
def originalCallback {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    BinaryTriangleExecution.PreparedOracle n (ComputableParameters.block n)
      (BinaryTriangleExecution.HistoryPayload n (ComputableParameters.block n)) :=
  BinaryTriangleExecution.prepareConcreteFromPrimes (EndToEndAPSP.block_pos n) p
    (ParameterMetadata.successfulLabels setup hsetup p hp)
    (ParameterMetadata.successfulLabels_eq setup hsetup p hp) a

theorem successRecord_setupBits {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (successRecord W a setup hsetup p hp).callback.setupBits=
      (originalCallback W a setup hsetup p hp).setupBits := by
  unfold successRecord originalCallback
  exact callback_setupBits a _ _ p _ _

theorem successRecord_setupControl {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (successRecord W a setup hsetup p hp).callback.setupControl=
      (originalCallback W a setup hsetup p hp).setupControl := by
  unfold successRecord originalCallback
  exact callback_setupControl a _ _ p _ _

theorem successRecord_work {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (A B T : IntTable n) :
    ((successRecord W a setup hsetup p hp).callback.oracle A B T).work=
      ((originalCallback W a setup hsetup p hp).oracle A B T).work := by
  unfold successRecord originalCallback
  exact callback_work a _ _ p _ _ A B T

theorem successRecord_answerWrites {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (A B T : IntTable n) :
    ((successRecord W a setup hsetup p hp).callback.oracle A B T).answerWrites=
      ((originalCallback W a setup hsetup p hp).oracle A B T).answerWrites := by
  unfold successRecord originalCallback
  exact callback_answerWrites a _ _ p _ _ A B T

theorem prepared_setupBits_original {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).setupBits=
      setup.bitSteps+publicSetupBits n W+(originalCallback W a setup hsetup p hp).setupBits := by
  rw [prepared_setupBits W a setup hsetup p hp,successRecord_setupBits W a setup hsetup p hp]

theorem prepared_setupControl_original {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) :
    (prepareFromSetup W a setup hsetup).setupControl=
      setup.metadata.pool.length+(originalCallback W a setup hsetup p hp).setupControl+64 := by
  rw [prepared_setupControl W a setup hsetup p hp,successRecord_setupControl W a setup hsetup p hp]

theorem prepared_work_original {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (A B T : IntTable n) :
    ((prepareFromSetup W a setup hsetup).oracle A B T).work=
      ((originalCallback W a setup hsetup p hp).oracle A B T).work+4*(a+1) := by
  rw [prepared_oracle W a setup hsetup p hp]
  change ((successRecord W a setup hsetup p hp).callback.oracle A B T).work+4*(a+1)=_
  rw [successRecord_work W a setup hsetup p hp A B T]

theorem prepared_answerWrites_original {n : ℕ} (W a : ℕ) (setup : ParameterExecution.Execution n (cap n W))
    (hsetup : setup=ParameterExecution.execute n (cap n W))
    (p : CompleteAPSP.Parameters (ComputableParameters.block n) (cap n W))
    (hp : setup.value=some p) (A B T : IntTable n) :
    ((prepareFromSetup W a setup hsetup).oracle A B T).answerWrites=
      ((originalCallback W a setup hsetup p hp).oracle A B T).answerWrites := by
  rw [prepared_oracle W a setup hsetup p hp]
  exact successRecord_answerWrites W a setup hsetup p hp A B T


#print axioms prepared_setupBits_original
#print axioms prepared_setupControl_original
#print axioms prepared_work_original
#print axioms prepared_answerWrites_original
#print axioms callback_setupBits
#print axioms callback_setupControl
#print axioms callback_work
#print axioms callback_answerWrites
#print axioms lifted_work
#print axioms lifted_answerWrites
#print axioms prepareFromSetup_of_some
#print axioms prepared_success_value
#print axioms prepared_oracle
#print axioms prepared_setupBits
#print axioms prepared_setupControl

end ThinMatrix.BinaryAlignedAPSPTransport
