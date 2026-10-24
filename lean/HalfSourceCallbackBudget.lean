import HalfSourceControllerWidths
import BinaryTriangleCosts

/-! Controller and final scan prices for an arbitrary correct production
backend. Its semantic count bound is explicit; there is no runtime premise. -/
namespace ThinMatrix.HalfSourceCallbackBudget
open BinaryTriangleExecution
open BinaryTriangleCosts (referenceBudget inputBits_of_polynomial_entry_cap polynomial_cap_size)
open BinaryTriangleCosts.FixedPrices (pool_positive)
open HalfSourceBatchFit HalfSourcePrimeParameters HalfSourceControllerWidths
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local irreducible] HalfSourceBatchFit.R HalfSourceBatchFit.block
variable {Payload : Type}

def scalarWidth (n κ : ℕ) : ℕ := controllerConstant κ 4*n.size
def addressPrice (n κ A : ℕ) : ℕ := BackendScalarBits.addressedUnit (scalarWidth n κ) (A*n.size)
def unitConstant (κ A : ℕ) : ℕ := 800*(controllerConstant κ 4+1)^2+100*(controllerConstant κ 4+A+2)^2

theorem unit_poly (n κ A : ℕ) : BinaryControllerExecution.executionUnit
    (scalarWidth n κ) (A*n.size) ≤ unitConstant κ A*(n.size+1)^2 :=
  BinaryControllerPolynomialBounds.executionUnit_poly _ _ _ _ _ le_rfl le_rfl

def controllerCoefficient (κ A : ℕ) : ℕ := unitConstant κ A*(512*(R+1)*(R+2)+101)
attribute [local irreducible] controllerCoefficient

theorem addressPrice_le_unit (n κ A : ℕ) : addressPrice n κ A ≤
    BinaryControllerExecution.executionUnit (scalarWidth n κ) (A*n.size) := Nat.le_add_left _ _

theorem addressPrice_poly (n κ A : ℕ) : addressPrice n κ A ≤ unitConstant κ A*(n.size+1)^2 :=
  (addressPrice_le_unit n κ A).trans (unit_poly n κ A)

theorem computed_primes_bound {n U : ℕ}
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters)
    (static : Static (n:=n) parameters) :
    ∀ i, (static.primes.get i).control ≤ 8*scale n := by
  intro i
  have he := congrArg (fun primes=>primes.get i) static.primes_eq
  simp only [BinaryControllerExecution.projectPrimes,Vector.get_map] at he
  change (static.primes.get i).control=(EndToEndAPSP.primeVector parameters.pool).get i at he
  rw [he]
  have hm := EndToEndAPSP.primeVector_mem parameters.pool i
  have hm' := Eq.mp (congrArg
    (fun s : Finset ℕ => (EndToEndAPSP.primeVector parameters.pool).get i ∈ s)
    (program_sound n U parameters hp).1) hm
  have hc := (Finset.mem_sdiff.mp hm').1
  rw [PrimePool.enumeratedCandidates_eq] at hc
  exact (PrimePool.candidate_upper hc).le

theorem computed_controller_price {n U κ addressCoefficient : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (block n) Payload)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hcounts : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) (block n)) :
    let addr := addressPrice n κ addressCoefficient
    (controllerExec backend parameters static A B T).bitSteps+
      addr*(controllerExec backend parameters static A B T).controlSites ≤ (controllerCoefficient κ addressCoefficient*(n.size+1)^2)*
        referenceBudget n (block n) parameters.pool.card parameters.k parameters.stages := by
  let addr := addressPrice n κ addressCoefficient
  let Bctrl := scalarWidth n κ
  let Abits := addressCoefficient*n.size
  let EU := BinaryControllerExecution.executionUnit Bctrl Abits
  have hparams := program_sound n U parameters hp
  have hk : parameters.k ≤ HalfSourceBatchFit.R := by
    rw [hparams.2.2.2.1]
    exact Nat.sub_le _ _
  have hwidth : BinaryTriangleCosts.Finite.controllerWidth n parameters (n^4) (8*scale n) ≤ Bctrl := by
    exact computed_controller_width n U (n^4) κ 4 hn parameters hp hU le_rfl
  have hpmax : 1 ≤ 8*scale n := by
    have hs := parameters.P_pos
    rw [hparams.2.1] at hs
    omega
  have hfinite := BinaryTriangleCosts.Finite.controllerExec_reference_price_of_width (W:=n^4) (Bctrl:=Bctrl) (by omega) backend parameters static
    A B T hcounts (computed_primes_bound parameters hp static) hpmax (pool_positive parameters) Abits hwidth
  have heu : EU ≤ unitConstant κ addressCoefficient*(n.size+1)^2 := unit_poly n κ addressCoefficient
  have ha : addr ≤ EU := addressPrice_le_unit n κ addressCoefficient
  have hF : 512*(parameters.k+1)*(parameters.k+2)+1 ≤ 512*(HalfSourceBatchFit.R+1)*(HalfSourceBatchFit.R+2)+1 := by gcongr
  have hcoef : EU*(512*(parameters.k+1)*(parameters.k+2)+1)+100*addr ≤ controllerCoefficient κ addressCoefficient*(n.size+1)^2 := by
    calc
      _ ≤ EU*(512*(HalfSourceBatchFit.R+1)*(HalfSourceBatchFit.R+2)+1)+100*EU :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hF) (Nat.mul_le_mul_left _ ha)
      _ = EU*(512*(HalfSourceBatchFit.R+1)*(HalfSourceBatchFit.R+2)+101) := by ring
      _ ≤ (unitConstant κ addressCoefficient*(n.size+1)^2)*
          (512*(HalfSourceBatchFit.R+1)*(HalfSourceBatchFit.R+2)+101) := Nat.mul_le_mul_right _ heu
      _ = _ := by unfold controllerCoefficient; ring
  exact hfinite.trans (Nat.mul_le_mul_right _ hcoef)


def callbackUnit (n κ addressCoefficient : ℕ) : ℕ :=
  controllerCoefficient κ addressCoefficient*(n.size+1)^2+
    scanUnit (κ*n.size+1)+BinaryTriangleCosts.Finite.capUnit (κ*n.size+1) (κ*n.size+1)+
    37*addressPrice n κ addressCoefficient+3

def callbackCoefficient (κ addressCoefficient : ℕ) : ℕ :=
  controllerCoefficient κ addressCoefficient+13000*(2*(κ+1)+6)^2+
    37*unitConstant κ addressCoefficient+3

attribute [local irreducible] callbackCoefficient

theorem callbackUnit_poly (n κ addressCoefficient : ℕ) :
    callbackUnit n κ addressCoefficient ≤ callbackCoefficient κ addressCoefficient*(n.size+1)^2 := by
  let u:=n.size+1
  have hu : 1 ≤ u := by dsimp [u];omega
  have hsum : (κ*n.size+1)+(κ*n.size+1)+6 ≤ (2*(κ+1)+6)*u := by dsimp [u];nlinarith
  have hscan : scanUnit (κ*n.size+1)+BinaryTriangleCosts.Finite.capUnit (κ*n.size+1) (κ*n.size+1) ≤ (13000*(2*(κ+1)+6)^2)*u^2 := by
    calc
      _ ≤ 13000*((κ*n.size+1)+(κ*n.size+1)+6)^2 := BinaryTriangleCosts.Finite.cap_scan_le _ _
      _ ≤ 13000*((2*(κ+1)+6)*u)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have haddr := Nat.mul_le_mul_left 37 (addressPrice_poly n κ addressCoefficient)
  have h3 : 3 ≤ 3*u^2 := Nat.le_mul_of_pos_right _ (one_le_pow₀ hu)
  unfold callbackUnit callbackCoefficient
  change controllerCoefficient κ addressCoefficient*u^2+scanUnit (κ*n.size+1)+
    BinaryTriangleCosts.Finite.capUnit (κ*n.size+1) (κ*n.size+1)+37*addressPrice n κ addressCoefficient+3 ≤ _
  calc
    _ = controllerCoefficient κ addressCoefficient*u^2+
        (scanUnit (κ*n.size+1)+BinaryTriangleCosts.Finite.capUnit (κ*n.size+1) (κ*n.size+1))+
        37*addressPrice n κ addressCoefficient+3 := by ring
    _ ≤ controllerCoefficient κ addressCoefficient*u^2+(13000*(2*(κ+1)+6)^2)*u^2+
        (37*unitConstant κ addressCoefficient)*u^2+3*u^2 := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hscan _)
        (by simpa only [u,Nat.mul_assoc] using haddr)) h3
    _ = _ := by dsimp [u];ring

theorem computed_callback_budget {n U κ addressCoefficient : ℕ} (hn : 3 ≤ n)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hU : U ≤ n^κ)
    (backend : Backend n (block n) Payload)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hcounts : BinaryControllerExecution.OracleCountsBound (backend.oracle A B T) (block n))
    (hcap : CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U) :
    let addr := addressPrice n κ addressCoefficient
    (callback backend parameters static addr A B T).work+
      (callback backend parameters static addr A B T).answerWrites ≤ (solve backend parameters static A B T).backendWork+
        (callbackCoefficient κ addressCoefficient*(n.size+1)^2)*referenceBudget n (block n)
          parameters.pool.card parameters.k parameters.stages := by
  let addr := addressPrice n κ addressCoefficient
  have hparams := program_sound n U parameters hp
  have hcontroller := computed_controller_price (addressCoefficient:=addressCoefficient) hn parameters hp hU backend static A B T hcounts
  have hfinite := BinaryTriangleCosts.Finite.callback_reference_price (by omega) (HalfSourceBatchFit.block_pos n)
    (HalfSourceBatchGeometry.block_le_n n (by omega)) backend parameters static hparams.2.2.2.2.2.ge
    addr (controllerCoefficient κ addressCoefficient*(n.size+1)^2) A B T
    (inputBits_of_polynomial_entry_cap A B T hU hcap) (polynomial_cap_size n U κ hU) hcap hcontroller
  exact hfinite.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (callbackUnit_poly n κ addressCoefficient)) _)

#print axioms unit_poly
#print axioms computed_primes_bound
#print axioms computed_controller_price
#print axioms callbackUnit_poly
#print axioms computed_callback_budget
end ThinMatrix.HalfSourceCallbackBudget
