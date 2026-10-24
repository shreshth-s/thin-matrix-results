import HalfSourceCallbackBudget

/-! Actual retained prime/count setup under the exact-half program. -/
namespace ThinMatrix.HalfSourcePreparedSetup
open BinaryTriangleExecution HalfSourceBatchFit HalfSourcePrimeParameters HalfSourceControllerWidths HalfSourceCallbackBudget
open BinaryTriangleCosts (referenceBudget)
open BinaryTriangleCosts.PreparedSetup (fromPrimes_setupBits_zero)
open BinaryControllerPolynomialBounds (input_size_bound)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.block
theorem computed_label_sizes {n U : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (HalfSourceBatchFit.block n) U)
    (hp : HalfSourcePrimeParameters.program n U = some parameters)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) :
    ∀ i, (labels.get i).size ≤ 14 * n.size + 1 := by
  have hs : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  have hpool := (HalfSourcePrimeParameters.program_sound n U parameters hp).1
  intro i
  rw [hlabels]
  have hm := EndToEndAPSP.primeVector_mem parameters.pool i
  have hm' := Eq.mp (congrArg
    (fun s : Finset ℕ => (EndToEndAPSP.primeVector parameters.pool).get i ∈ s) hpool) hm
  have hc := HalfSourceBackendAggregation.pool_subset n hm'
  have hbound : (EndToEndAPSP.primeVector parameters.pool).get i ≤ 2^(14*n.size) :=
    (PrimePool.candidate_upper hc).le.trans (eightScale_pow n hs)
  exact (Nat.size_le_size hbound).trans_eq Nat.size_pow

theorem fromPrimes_setupControl_bound {n U κ : ℕ} {Payload : Type} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (HalfSourceBatchFit.block n) U)
    (hp : HalfSourcePrimeParameters.program n U = some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (HalfSourceBatchFit.block n) Payload)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) (addr : ℕ) :
    (prepareOracleFromPrimes backend parameters labels hlabels addr).setupControl ≤
      (16*κ+500) * (n.size+1) *
        referenceBudget n (HalfSourceBatchFit.block n) parameters.pool.card
          parameters.k parameters.stages := by
  let P := parameters.pool.card
  let I := EndToEndAPSP.incidenceSize n (HalfSourceBatchFit.block n)
  let L := n.size + 1
  let C := 16*κ+500
  let R := referenceBudget n (HalfSourceBatchFit.block n) P parameters.k parameters.stages
  have hlabelsBound := computed_label_sizes hn parameters hp labels hlabels
  have hstatic := setupStaticFromPrimes_control_public (n:=n) parameters labels hlabels hlabelsBound
  have hhsize : (HalfSourceBatchFit.block n).size ≤ n.size :=
    Nat.size_le_size (HalfSourceBatchGeometry.block_le_n n (by omega))
  have hUsize : U.size ≤ κ*n.size+1 := input_size_bound n U κ hU
  have hlam : parameters.lam = U.size :=
    (HalfSourcePrimeParameters.program_sound n U parameters hp).2.2.1
  have hlamsize : parameters.lam.size ≤ κ*n.size+1 := by
    rw [hlam]
    exact (ParameterExecution.size_le_self U.size).trans hUsize
  have hPcoef : 8*(14*n.size+1)+19 ≤ C*L := by dsimp only [C,L]; nlinarith
  have hIcoef : 8*(HalfSourceBatchFit.block n).size+61 ≤ C*L := by
    dsimp only [C,L]
    nlinarith
  have hrest : 8*parameters.lam.size+8*U.size+21 ≤ C*L := by
    dsimp only [C,L]
    nlinarith
  have hR : P+I+1 ≤ R := by
    have hn2 : 1 ≤ n^2 := by nlinarith only [hn]
    dsimp only [R, referenceBudget, AlignedAPSPCosts.ControllerCosts.referenceControllerBudget, I]
    omega
  have hfull : (prepareOracleFromPrimes backend parameters labels hlabels addr).setupControl ≤
      P*(8*(14*n.size+1)+19)+I*(8*(HalfSourceBatchFit.block n).size+61)+
        (8*parameters.lam.size+8*U.size+21) := by
    change (setupStaticFromPrimes (n:=n) parameters labels hlabels).controlSites+P+1 ≤ _
    calc
      _ ≤ (P*(8*(14*n.size+1)+18)+I*(8*(HalfSourceBatchFit.block n).size+61)+
          8*parameters.lam.size+8*U.size+20)+P+1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hstatic P) 1
      _ = _ := by ring
  calc
    _ ≤ P*(8*(14*n.size+1)+19)+I*(8*(HalfSourceBatchFit.block n).size+61)+
        (8*parameters.lam.size+8*U.size+21) := hfull
    _ ≤ P*(C*L)+I*(C*L)+C*L :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left P hPcoef)
        (Nat.mul_le_mul_left I hIcoef)) hrest
    _ = C*L*(P+I+1) := by ring
    _ ≤ C*L*R := Nat.mul_le_mul_left _ hR

theorem fromPrimes_setup_price {n U κ degree : ℕ} {Payload : Type} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (HalfSourceBatchFit.block n) U)
    (hp : HalfSourcePrimeParameters.program n U = some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (HalfSourceBatchFit.block n) Payload)
    (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels = EndToEndAPSP.primeVector parameters.pool) :
    let prepared := prepareOracleFromPrimes backend parameters labels hlabels (addressPrice n κ degree)
    prepared.setupBits + addressPrice n κ degree * prepared.setupControl ≤
      (unitConstant κ degree * (16*κ+500)) * (n.size+1)^3 *
        referenceBudget n (HalfSourceBatchFit.block n) parameters.pool.card
          parameters.k parameters.stages := by
  dsimp only
  rw [fromPrimes_setupBits_zero, zero_add]
  have haddr := addressPrice_poly n κ degree
  have hc := fromPrimes_setupControl_bound hn parameters hp hU backend labels hlabels
    (addressPrice n κ degree)
  apply (Nat.mul_le_mul haddr hc).trans_eq
  ring


#print axioms computed_label_sizes
#print axioms fromPrimes_setupControl_bound
#print axioms fromPrimes_setup_price
end ThinMatrix.HalfSourcePreparedSetup
