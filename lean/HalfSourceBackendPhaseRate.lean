import HalfSourceBackendCostAssembly
import HalfSourceSetupPhaseRate

/-! Unconditional actual exact-half phase cost: one fixed proved valid CW
backend, with every source, setup, completion, query, output and address-price
charge discharged. The universal logarithmic factor is absorbed by the
strict, exact-rational 61-inequality phase certificate in the APSP host. -/
namespace ThinMatrix.HalfSourceBackendPhaseRate
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
noncomputable section

 theorem exists_phase_prices : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    ∃ hv : scheme.Valid, ∀ κ A : ℕ, ∃ C : ℝ, 0<C ∧
      GraphHalfSourceHostCosts.phasePrices scheme hnum hden hz hv κ A 42 C := by
  obtain ⟨scheme,hnum,hden,hz,hvalid,Cl,hCl,hlow⟩ := HalfSourceLowPhaseRate.exists_phase_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,?_⟩
  intro κ A
  obtain ⟨Cs,hCs,hsetup⟩ := HalfSourceSetupPhaseRate.exists_setup_rate scheme κ
  let C := HalfSourceBackendCostAssembly.coefficient scheme κ A Cs Cl
  have hh : 0≤HalfSourceHighExecutionRate.coefficient scheme κ := by
    unfold HalfSourceHighExecutionRate.coefficient
    have hc := HalfSourceHighBlockCost.constant_nonneg
    positivity
  have ho := HalfSourceOutputPhaseRate.coefficient_pos scheme κ
  refine ⟨C,?_,?_⟩
  · dsimp[C,HalfSourceBackendCostAssembly.coefficient]
    positivity
  · exact HalfSourceBackendCostAssembly.phase_prices scheme hnum hden hz hvalid κ A Cs Cl hCs hCl hsetup hlow

#print axioms exists_phase_prices
end
end ThinMatrix.HalfSourceBackendPhaseRate
