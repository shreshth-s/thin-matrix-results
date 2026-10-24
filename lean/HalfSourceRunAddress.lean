import HalfSourceRetainedHeap
import HalfSourceAPSPHost
import GraphCallbackOutputStorage
import HalfSourceBackendAggregation

namespace ThinMatrix.HalfSourceRunAddress
open HalfSourceBatchFit HalfSourcePrimeParameters
open BinaryControllerPolynomialBounds (hostStorageMultiplicity hostExponent)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000
noncomputable section

theorem output_in_payload {n h r : ℕ} (scheme : RectangularBatch.Scheme)
    (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (S : ℕ) (hh : 0 < h) :
    GraphCallbackOutputStorage.cells f p ≤ GraphCallbackStorage.payload f p scheme (S:=S) := by
  have ho := GraphCallbackOutputStorage.bound f p scheme hh
  apply ho.trans
  unfold GraphCallbackStorage.payload
  dsimp only
  have hf : 1 ≤ 64*(CompactBlocks.blockCount n h+1)*(GraphCallbackStorage.types f p+1) :=
    Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _)
  apply le_trans ?_ (Nat.le_mul_of_pos_left _ hf)
  have hg : 1 ≤ GraphOwnBandPriced.G f p (S:=S)+1 := by omega
  have hx := Nat.le_mul_of_pos_left
    (2^(9*GraphOwnBandStorage.scale scheme (GraphOwnBandShapeBounds.width f p)+21)+1) hg
  omega

theorem phase_layout (scheme : RectangularBatch.Scheme) (n : ℕ)
    (call : Call n) (hn : 3 ≤ n) (hv : EndToEndAPSP.ValidFactors call.factors) :
    let out := HalfSourceDispatch.prepare n (block n) call.factors hv
    GraphCallbackStorage.payload out.split.plan out.plan.value scheme
      (S:=HalfSourcePublicFit.bands out.split.plan out.plan.value) ≤
        HalfSourceAddressGeometry.singlePayload scheme n ∧
    GraphCallbackOutputStorage.cells out.split.plan out.plan.value ≤
        HalfSourceAddressGeometry.singlePayload scheme n := by
  intro out
  have hp := HalfSourceAddressGeometry.payload_bound scheme n call hn hv
  exact ⟨hp,(output_in_payload scheme out.split.plan out.plan.value _ (block_pos n)).trans hp⟩

/-- Every actual retained controller call has a valid computed phase, whose
source/root layout and full cyclic/output layout fit the reserved payload. -/
theorem callback_layout (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory) {n U : ℕ} (a : ℕ) (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U = some parameters)
    (static : BinaryTriangleExecution.Static (n:=n) parameters)
    (X Y T : BinaryTriangleExecution.IntTable n)
    (c : BinaryControllerExecution.Call (EndToEndAPSP.incidenceSize n (block n))
      (factory.Payload n (block n)))
    (hc : c ∈ (BinaryTriangleExecution.solve
      (factory.backend n (block n) a (block_pos n)) parameters static X Y T).calls) :
    ∃ phase : Call n, phase.factors = c.factors.selected ++ [c.factors.candidate] ∧
      ∃ hv : EndToEndAPSP.ValidFactors phase.factors,
        let out := HalfSourceDispatch.prepare n (block n) phase.factors hv
        GraphCallbackStorage.payload out.split.plan out.plan.value scheme
          (S:=HalfSourcePublicFit.bands out.split.plan out.plan.value) ≤
            HalfSourceAddressGeometry.singlePayload scheme n ∧
        GraphCallbackOutputStorage.cells out.split.plan out.plan.value ≤
            HalfSourceAddressGeometry.singlePayload scheme n := by
  let backend := factory.backend n (block n) a (block_pos n)
  have hs := program_sound n U parameters hp
  have hpool := hs.1
  have hk : parameters.k+1=R := by
    rw [hs.2.2.2.1]
    exact Nat.sub_add_cancel (by norm_num [HalfSourceBatchFit.R])
  have hlen : (c.factors.selected ++ [c.factors.candidate]).length ≤ R := by
    have h := BinaryTriangleExecution.solve_factors_length backend parameters static X Y T c hc
    simpa only [List.length_append,List.length_singleton,hk] using h
  have hmem : ∀ p ∈ c.factors.selected ++ [c.factors.candidate], p ∈ computedPool n := by
    intro p hm
    rw [←hpool]
    exact BinaryTriangleExecution.solve_factor_property backend parameters static X Y T
      (fun p => p ∈ parameters.pool) (fun _ h => h) c hc p hm
  let phase := HalfSourceBackendAggregation.phaseOfPool n
    (c.factors.selected ++ [c.factors.candidate]) hlen hmem
  have hthree : ∀ p ∈ parameters.pool, p ≠ 3 := by
    intro p hm he
    rw [hpool] at hm
    exact (Finset.mem_sdiff.mp hm).2 (by simp only [he,Finset.mem_singleton])
  have hv := BinaryTriangleExecution.solve_valid_histories backend parameters static X Y T hthree c hc
  exact ⟨phase,rfl,hv,phase_layout scheme n phase hn hv⟩

def hostSlots (factory : HalfSourceAPSPHost.BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a degree : ℕ) : ℕ :=
  (HalfSourceAPSPHost.run factory w W a).core.calls.length * hostStorageMultiplicity n degree

theorem hostSlots_bound (factory : HalfSourceAPSPHost.BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a degree : ℕ)
    (hn : 3 ≤ n) (hW : W ≤ n^degree) :
    hostSlots factory w W a degree ≤ 2^(hostExponent degree*n.size) := by
  exact BinaryControllerPolynomialBounds.binary_host_storage_pow
    (HalfSourceAPSPHost.prepare factory n W a).oracle
    (BinaryAPSPCaller.encodeGraph w).value W degree
    (Nat.size_pos.mpr (by omega)) hW

/-- Retain the actual host trace, with a proved uniform capacity for each
controller callback. The capacity covers every candidate and restart. -/
def completeHeap (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory) {n U : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a κ degree : ℕ)
    (parameters : CompleteAPSP.Parameters (block n) U) : ℕ :=
  HalfSourceRetainedHeap.retainedHeap scheme κ (hostSlots factory w W a degree)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) parameters

theorem completeHeap_price (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory) {n U : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a κ degree : ℕ)
    (hn : 3 ≤ n) (hW : W ≤ n^degree)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U = some parameters) (x j : ℕ)
    (hx : x < completeHeap scheme factory w W a κ degree parameters)
    (hj : j < completeHeap scheme factory w W a κ degree parameters) :
    BackendScalarBits.addressedUnit x.size j.size ≤
      HalfSourceCallbackBudget.addressPrice n κ
        (2*HalfSourceRetainedHeap.addressConstant scheme κ degree) :=
  HalfSourceRetainedHeap.indexed_price scheme κ degree _ _ x j hn parameters hp
    le_rfl (hostSlots_bound factory w W a degree hn hW) hx hj

/-- The actual solved callback needs no supplied call-count bound. -/
theorem callbackHeap_price (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory) {n U : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a κ degree : ℕ)
    (hn : 3 ≤ n) (hW : W ≤ n^degree)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U = some parameters)
    (static : BinaryTriangleExecution.Static (n:=n) parameters)
    (X Y T : BinaryTriangleExecution.IntTable n) (x j : ℕ)
    (hx : x < HalfSourceRetainedHeap.retainedHeap scheme κ (hostSlots factory w W a degree)
      (BinaryTriangleExecution.solve (factory.backend n (block n) a (block_pos n))
        parameters static X Y T).calls.length parameters)
    (hj : j < HalfSourceRetainedHeap.retainedHeap scheme κ (hostSlots factory w W a degree)
      (BinaryTriangleExecution.solve (factory.backend n (block n) a (block_pos n))
        parameters static X Y T).calls.length parameters) :
    BackendScalarBits.addressedUnit x.size j.size ≤
      HalfSourceCallbackBudget.addressPrice n κ
        (2*HalfSourceRetainedHeap.addressConstant scheme κ degree) :=
  HalfSourceRetainedHeap.indexed_price scheme κ degree _ _ x j hn parameters hp
    (BinaryTriangleExecution.solve_calls_bound _ parameters static X Y T)
    (hostSlots_bound factory w W a degree hn hW) hx hj

theorem prepared_setup (factory : HalfSourceAPSPHost.BackendFactory) {n : ℕ}
    (W a : ℕ) (setup : HalfSourceParameterExecution.Execution n (HalfSourceAPSPHost.cap n W))
    (hs : setup = HalfSourceParameterExecution.execute n (HalfSourceAPSPHost.cap n W)) :
    (HalfSourceAPSPHost.prepareFromSetup factory W a setup hs).setup = setup := by
  unfold HalfSourceAPSPHost.prepareFromSetup
  split <;> rfl

theorem preparation_value (factory : HalfSourceAPSPHost.BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W a : ℕ) :
    (HalfSourceAPSPHost.run factory w W a).preparation.setup.value =
      program n (HalfSourceAPSPHost.cap n W) := by
  simp only [HalfSourceAPSPHost.run,HalfSourceAPSPHost.prepare,prepared_setup,
    HalfSourceParameterExecution.execute_value]

def selectedPrice (scheme : RectangularBatch.Scheme) (degree n : ℕ) : ℕ :=
  HalfSourceCallbackBudget.addressPrice n (degree+2)
    (2*HalfSourceRetainedHeap.addressConstant scheme (degree+2) degree)

/-- The selected run's own parameter output and host trace determine this
layout; the predicate has no externally supplied successful setup or widths. -/
def AddressSafe (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory) {n : ℕ}
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ) : Prop :=
  ∃ parameters : CompleteAPSP.Parameters (block n) (HalfSourceAPSPHost.cap n W),
    (HalfSourceAPSPHost.run factory w W (selectedPrice scheme degree n)).preparation.setup.value =
      some parameters ∧
    ∀ x j : ℕ,
      x < completeHeap scheme factory w W (selectedPrice scheme degree n) (degree+2) degree parameters →
      j < completeHeap scheme factory w W (selectedPrice scheme degree n) (degree+2) degree parameters →
      BackendScalarBits.addressedUnit x.size j.size ≤ selectedPrice scheme degree n

theorem eventual_addresses (scheme : RectangularBatch.Scheme)
    (factory : HalfSourceAPSPHost.BackendFactory)
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hW : ∀ n, W n ≤ n^degree) :
    ∀ᶠ n : ℕ in Filter.atTop, AddressSafe scheme factory (w n) (W n) degree := by
  filter_upwards [eventually_program_apspCap degree,Filter.eventually_ge_atTop (3:ℕ)] with n hs hn
  have hsome := hs (W n) (hW n)
  cases hp : program n (HalfSourceAPSPHost.cap n (W n)) with
  | none => simp only [HalfSourceAPSPHost.cap] at hp; rw [hp] at hsome; contradiction
  | some parameters =>
    refine ⟨parameters,?_,?_⟩
    · rw [preparation_value,hp]
    · intro x j hx hj
      exact completeHeap_price scheme factory (w n) (W n) (selectedPrice scheme degree n)
        (degree+2) degree hn (hW n) parameters hp x j hx hj

#print axioms hostSlots_bound
#print axioms output_in_payload
#print axioms phase_layout
#print axioms callback_layout
#print axioms completeHeap_price
#print axioms callbackHeap_price
#print axioms preparation_value
#print axioms prepared_setup
#print axioms eventual_addresses
end
end ThinMatrix.HalfSourceRunAddress
