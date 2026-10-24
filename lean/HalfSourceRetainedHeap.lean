import HalfSourceAddressGeometry
import HalfSourceControllerWidths
import HalfSourceCallbackBudget

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.HalfSourceRetainedHeap
open HalfSourceBatchFit HalfSourcePrimeParameters HalfSourceAddressGeometry
open BinaryControllerPolynomialBounds (pow_coeff_mono incidence_pow stages_pow hostExponent)
open HalfSourceControllerWidths
noncomputable section
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.block shapeConstant scaleConstant payloadConstant

/-- A uniform physical field capacity, including the fourth-degree greedy
score numerators, source/setup coefficients and the recursive matrix fields.
This is a bit-length bound, not a unit-cost arithmetic assumption. -/
def fieldCoefficient (scheme : RectangularBatch.Scheme) (κ : ℕ) :=
  scaleConstant scheme+controllerConstant κ 4+κ+1024*(shapeConstant+1)^4+100

def fieldWidth (scheme : RectangularBatch.Scheme) (n κ : ℕ) :=
  fieldCoefficient scheme κ*(n.size+1)^4

def fieldExponent (scheme : RectangularBatch.Scheme) (κ : ℕ) := fieldCoefficient scheme κ+4

attribute [local irreducible] fieldCoefficient fieldWidth fieldExponent

 theorem field_pow (scheme : RectangularBatch.Scheme) (n κ : ℕ) (hs : 1≤ n.size) :
    fieldWidth scheme n κ≤ 2^(fieldExponent scheme κ*n.size) := by
  have hc : fieldCoefficient scheme κ≤ 2^(fieldCoefficient scheme κ) := Nat.lt_two_pow_self.le
  have hn : n.size+1≤ 2^n.size := Nat.lt_two_pow_self
  unfold fieldWidth fieldExponent
  calc
    _ ≤  2^(fieldCoefficient scheme κ)*(2^n.size)^4 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hn 4)
    _ = 2^(fieldCoefficient scheme κ+4*n.size) := by
      rw [←pow_mul,←pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have hc0 := Nat.le_mul_of_pos_right (fieldCoefficient scheme κ) hs
      rw [Nat.add_mul]
      omega)


 theorem scores_width (m : ℕ) : HalfSourceBinaryScores.width m≤ 1024*(m+1)^4 := by
  unfold HalfSourceBinaryScores.width HalfSourceIntegerScores.A HalfSourceIntegerScores.K
  ring_nf
  omega


 theorem score_fields (scheme : RectangularBatch.Scheme) (n κ m : ℕ) (hm : m≤ shapeConstant*n.size) :
    HalfSourceBinaryScores.width m≤ fieldWidth scheme n κ := by
  unfold fieldWidth
  have hm' : m+1≤ (shapeConstant+1)*(n.size+1) := by nlinarith
  have hp := Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hm' 4)
  have hc : 1024*(shapeConstant+1)^4≤ fieldCoefficient scheme κ := by unfold fieldCoefficient;omega
  calc
    _ ≤  1024*(m+1)^4 := scores_width m
    _ ≤  1024*((shapeConstant+1)*(n.size+1))^4 := hp
    _ = (1024*(shapeConstant+1)^4)*(n.size+1)^4 := by ring
    _ ≤  _ := Nat.mul_le_mul_right _ hc


 theorem linear_fields (scheme : RectangularBatch.Scheme) (n κ : ℕ) :
    scaleConstant scheme*n.size≤ fieldWidth scheme n κ ∧
    HalfSourceCallbackBudget.scalarWidth n κ≤ fieldWidth scheme n κ ∧
    κ*n.size+1≤ fieldWidth scheme n κ := by
  unfold fieldWidth
  have hp : n.size+1≤ (n.size+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤n.size+1) (by decide : 1≤4)
  have hscale : scaleConstant scheme≤ fieldCoefficient scheme κ := by unfold fieldCoefficient;omega
  have hctrl : controllerConstant κ 4≤ fieldCoefficient scheme κ := by unfold fieldCoefficient;omega
  have hk : κ+1≤ fieldCoefficient scheme κ := by unfold fieldCoefficient;omega
  refine ⟨?_,?_,?_⟩
  · exact Nat.mul_le_mul hscale (show n.size≤ (n.size+1)^4 from (Nat.le_succ _).trans hp)
  · exact Nat.mul_le_mul hctrl (show n.size≤ (n.size+1)^4 from (Nat.le_succ _).trans hp)
  · have hh : κ*n.size+1≤ (κ+1)*(n.size+1) := by nlinarith
    exact hh.trans (Nat.mul_le_mul hk hp)



 def addressConstant (scheme : RectangularBatch.Scheme) (κ degree : ℕ) :=
  payloadConstant scheme+1+(2+R+14)+hostExponent degree+14+5+2+fieldExponent scheme κ+18

 def retainedHeap {n U : ℕ} (scheme : RectangularBatch.Scheme) (κ hostCalls callbackCalls : ℕ)
    (parameters : CompleteAPSP.Parameters (block n) U) :=
  ControllerHeapPow.heapBitCells (singlePayload scheme n) (CompactBlocks.blockCount n (block n))
    callbackCalls hostCalls parameters.pool.card (EndToEndAPSP.incidenceSize n (block n)) (n*n)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) (fieldWidth scheme n κ)

attribute [local irreducible] addressConstant retainedHeap

 theorem heap_bound {n U : ℕ} (scheme : RectangularBatch.Scheme) (κ degree hostCalls callbackCalls : ℕ)
    (hn : 3≤ n) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters)
    (hcalls : callbackCalls≤ parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤ 2^(hostExponent degree*n.size)) :
    retainedHeap scheme κ hostCalls callbackCalls parameters≤ 2^((addressConstant scheme κ degree-1)*n.size) := by
  have hs : 1≤ n.size := Nat.size_pos.mpr (by omega)
  rcases program_sound n U parameters hp with ⟨hpool,hscale,hlam,hk,hM,hstages⟩
  have hR : 1≤ R := by norm_num [HalfSourceBatchFit.R]
  have hkp : parameters.k+1=R := by rw [hk,Nat.sub_add_cancel hR]
  have hr : R≤ 2^(R*n.size) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hs))
  have hcap : parameters.stages*(parameters.k+1)*parameters.pool.card≤ 2^((2+R+14)*n.size) := by
    rw [hstages,hkp,hpool]
    calc
      _ ≤  2^(2*n.size)*2^(R*n.size)*2^(14*n.size) :=
        Nat.mul_le_mul (Nat.mul_le_mul (stages_pow n hs) hr) (computed_pool_pow n hs)
      _ = _ := by rw [←pow_add,←pow_add];congr 1;ring
  have hblocks : CompactBlocks.blockCount n (block n)≤ 2^(1*n.size) := by
    simpa only [Nat.one_mul,CompactBlocks.blockCount] using ((ceilDiv_le_iff_le_mul (block_pos n)).mpr
      (Nat.le_mul_of_pos_left n (block_pos n))).trans (Nat.lt_size_self n).le
  have hQ : n*n≤ 2^(2*n.size) := by
    exact (Nat.mul_le_mul (Nat.lt_size_self n).le (Nat.lt_size_self n).le).trans_eq (by ring)
  have hh := ControllerHeapPow.heapBitCells_le_pow n (singlePayload scheme n)
    (CompactBlocks.blockCount n (block n)) callbackCalls hostCalls parameters.pool.card
    (EndToEndAPSP.incidenceSize n (block n)) (n*n)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) (fieldWidth scheme n κ)
    (payloadConstant scheme) 1 (2+R+14) (hostExponent degree) 14 5 2 (fieldExponent scheme κ)
    hs le_rfl hblocks hcalls hcap hhost (by rw [hpool];exact computed_pool_pow n hs)
    (incidence_pow n (block n) (block_pos n) hs) hQ (field_pow scheme n κ hs)
  unfold retainedHeap
  apply hh.trans_eq
  unfold addressConstant
  rw [Nat.add_sub_assoc (by decide : 1≤18)]



 theorem address_width {n U : ℕ} (scheme : RectangularBatch.Scheme) (κ degree hostCalls callbackCalls j : ℕ)
    (hn : 3≤ n) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters)
    (hcalls : callbackCalls≤ parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤ 2^(hostExponent degree*n.size))
    (hj : j<retainedHeap scheme κ hostCalls callbackCalls parameters) :
    j.size≤ addressConstant scheme κ degree*n.size := by
  have hs : 1≤ n.size := Nat.size_pos.mpr (by omega)
  have hh := (Nat.size_le_size (hj.le.trans (heap_bound scheme κ degree hostCalls callbackCalls hn parameters hp hcalls hhost))).trans_eq Nat.size_pow
  have hc : 1≤ addressConstant scheme κ degree := by unfold addressConstant;omega
  calc
    _ ≤ (addressConstant scheme κ degree-1)*n.size+1 := hh
    _ ≤ (addressConstant scheme κ degree-1)*n.size+n.size := Nat.add_le_add_left hs _
    _ = addressConstant scheme κ degree*n.size := by
      rw [←Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel hc]


/-- The same fixed address coefficient prices the concrete backend and
controller; the logarithmic scalar bound comes from the controller cap. -/

 theorem address_price {n U : ℕ} (scheme : RectangularBatch.Scheme) (κ degree hostCalls callbackCalls x j : ℕ)
    (hn : 3≤ n) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters)
    (hcalls : callbackCalls≤ parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤ 2^(hostExponent degree*n.size))
    (hx : x.size≤ HalfSourceCallbackBudget.scalarWidth n κ)
    (hj : j<retainedHeap scheme κ hostCalls callbackCalls parameters) :
    BackendScalarBits.addressedUnit x.size j.size≤
      HalfSourceCallbackBudget.addressPrice n κ (addressConstant scheme κ degree) := by
  have hw := address_width scheme κ degree hostCalls callbackCalls j hn parameters hp hcalls hhost hj
  unfold HalfSourceCallbackBudget.addressPrice BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  gcongr


/-- Bounded-index control can use the global heap width for both its register
and its address. Doubling the fixed address coefficient covers these two
operands even when the controller's scalar cap is smaller. -/
 theorem indexed_price {n U : ℕ} (scheme : RectangularBatch.Scheme) (κ degree hostCalls callbackCalls x j : ℕ)
    (hn : 3≤n) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters)
    (hcalls : callbackCalls≤parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤2^(hostExponent degree*n.size))
    (hx : x<retainedHeap scheme κ hostCalls callbackCalls parameters)
    (hj : j<retainedHeap scheme κ hostCalls callbackCalls parameters) :
    BackendScalarBits.addressedUnit x.size j.size≤
      HalfSourceCallbackBudget.addressPrice n κ (2*addressConstant scheme κ degree) := by
  have hxw := address_width scheme κ degree hostCalls callbackCalls x hn parameters hp hcalls hhost hx
  have hjw := address_width scheme κ degree hostCalls callbackCalls j hn parameters hp hcalls hhost hj
  unfold HalfSourceCallbackBudget.addressPrice BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  have hb : x.size+j.size+1+1≤HalfSourceCallbackBudget.scalarWidth n κ+
      2*addressConstant scheme κ degree*n.size+1+1 := by
    rw [Nat.mul_assoc]
    omega
  exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hb 2)

#print axioms linear_fields
#print axioms heap_bound
#print axioms address_width
#print axioms address_price
#print axioms field_pow
#print axioms scores_width
#print axioms score_fields
#print axioms indexed_price
end
end ThinMatrix.HalfSourceRetainedHeap
