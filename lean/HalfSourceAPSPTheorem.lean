import GraphHalfSourceWork
import HalfSourceBackendPhaseRate
import HalfSourceRunAddress

/-!
# Exact-half deterministic integer APSP: correctness and complete charged work

One fixed rectangular multiplication scheme is selected from the proved
existence theorem. Its validity and every phase cost are discharged below.
The work model counts the actual binary coefficient programs and bounded
indexed-array/control actions, with a fixed input-promise-dependent address
price. It does not identify these counters with Lean native elapsed time or
assert a separate compiler-to-RAM theorem.
-/
namespace ThinMatrix.HalfSourceAPSPTheorem
open Filter Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section

def scheme : RectangularBatch.Scheme :=
  Classical.choose HalfSourceBackendPhaseRate.exists_phase_prices

theorem scheme_num : scheme.num = 861 :=
  Classical.choose (Classical.choose_spec HalfSourceBackendPhaseRate.exists_phase_prices)

theorem scheme_den : scheme.den = 500 :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec HalfSourceBackendPhaseRate.exists_phase_prices))

theorem scheme_z : scheme.z = 15 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec HalfSourceBackendPhaseRate.exists_phase_prices)))

theorem scheme_valid : scheme.Valid :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec HalfSourceBackendPhaseRate.exists_phase_prices))))

theorem phase_prices (κ A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ GraphHalfSourceHostCosts.phasePrices
      scheme scheme_num scheme_den scheme_z scheme_valid κ A 42 C :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec HalfSourceBackendPhaseRate.exists_phase_prices)))) κ A

def addressCoefficient (degree : ℕ) : ℕ :=
  2 * HalfSourceRetainedHeap.addressConstant scheme (degree+2) degree

def addressPrice (degree n : ℕ) : ℕ :=
  HalfSourceCallbackBudget.addressPrice n (degree+2) (addressCoefficient degree)

theorem addressPrice_eq_selectedPrice (degree n : ℕ) :
    addressPrice degree n = HalfSourceRunAddress.selectedPrice scheme degree n := rfl

def factory : HalfSourceAPSPHost.BackendFactory :=
  GraphHalfSourceHostCosts.factory scheme scheme_num scheme_den scheme_z scheme_valid

def run {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ) :=
  HalfSourceAPSPHost.run factory w W (addressPrice degree n)

attribute [local irreducible] scheme addressCoefficient

theorem one_le_addressPrice (degree n : ℕ) : 1 ≤ addressPrice degree n := by
  unfold addressPrice HalfSourceCallbackBudget.addressPrice
  exact BinaryAPSPPublicCostBounds.one_le_addressedUnit _ _

theorem addressPrice_poly (degree n : ℕ) :
    addressPrice degree n ≤
      HalfSourceCallbackBudget.unitConstant (degree+2) (addressCoefficient degree)*(n.size+1)^2 :=
  HalfSourceCallbackBudget.addressPrice_poly n (degree+2) (addressCoefficient degree)

theorem run_correct {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W)
    (hno : APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode w)) :
    APSPReduction.IsAPSP (StoredMinPlusAPSP.decode w)
      (StoredMinPlusAPSP.decode (BinaryAPSPCaller.viewOptional
        (run w W degree).core.value)) :=
  HalfSourceAPSPHost.run_correct factory w W (addressPrice degree n) hw hno

/-- Complete work for the selected concrete program. Only the input weight
promise remains; no source-cost, batch-fit, backend, or final-runtime premise
is supplied by the caller. -/
theorem run_work_bigO
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) :
    (fun n : ℕ => ((run (w n) (W n) degree).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) := by
  obtain ⟨C,hC,hphase⟩ := phase_prices (degree+2) (addressCoefficient degree)
  exact GraphHalfSourceWork.run_work_of_phasePrices
    scheme scheme_num scheme_den scheme_z scheme_valid degree
    (addressCoefficient degree) 42 C hC.le hphase w W hw hW

theorem correctness_and_work
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree)
    (hno : ∀ n, APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode (w n))) :
    (∀ n, APSPReduction.IsAPSP (StoredMinPlusAPSP.decode (w n))
      (StoredMinPlusAPSP.decode (BinaryAPSPCaller.viewOptional
        (run (w n) (W n) degree).core.value))) ∧
    (fun n : ℕ => ((run (w n) (W n) degree).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ)) :=
  ⟨fun n => run_correct (w n) (W n) degree (hw n) (hno n),
    run_work_bigO w W degree hw hW⟩

theorem eventual_addresses
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hW : ∀ n, W n ≤ n^degree) :
    ∀ᶠ n : ℕ in atTop, HalfSourceRunAddress.AddressSafe scheme factory (w n) (W n) degree :=
  HalfSourceRunAddress.eventual_addresses scheme factory w W degree hW

/-- Address prices cover the selected program's proved retained layout as
well as its complete charged work. This is not a compiler/allocation theorem. -/
theorem correctness_work_and_addresses
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree)
    (hno : ∀ n, APSPReduction.NoNegativeCycles (StoredMinPlusAPSP.decode (w n))) :
    (∀ n, APSPReduction.IsAPSP (StoredMinPlusAPSP.decode (w n))
      (StoredMinPlusAPSP.decode (BinaryAPSPCaller.viewOptional
        (run (w n) (W n) degree).core.value))) ∧
    ((fun n : ℕ => ((run (w n) (W n) degree).work:ℝ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^(14963431313/5000000000:ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, HalfSourceRunAddress.AddressSafe scheme factory (w n) (W n) degree) :=
  ⟨fun n => run_correct (w n) (W n) degree (hw n) (hno n),
    run_work_bigO w W degree hw hW,eventual_addresses w W degree hW⟩

#print axioms scheme_num
#print axioms scheme_den
#print axioms scheme_z
#print axioms scheme_valid
#print axioms phase_prices
#print axioms addressPrice_eq_selectedPrice
#print axioms one_le_addressPrice
#print axioms addressPrice_poly
#print axioms run_correct
#print axioms run_work_bigO
#print axioms correctness_and_work
#print axioms eventual_addresses
#print axioms correctness_work_and_addresses
end
end ThinMatrix.HalfSourceAPSPTheorem
