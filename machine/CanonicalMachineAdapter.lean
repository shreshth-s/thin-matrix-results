import MachineAdapter
import CoreCompatibility

/-!
# Canonical ledger to actual machine executions

This adapter combines the closed analytic cost certificate with an actual
Light min-plus solver. Its remaining hypothesis is the execution-cost bound
for that solver and the concrete upstream APSP controller, uniform in each
fixed input-magnitude exponent. This file supplies no such solver or bound.
-/

namespace ThinMatrix.CanonicalMachineAdapter

open Filter Asymptotics
open ThreeSumApsp ThreeSumApsp.WordRam

/-- Precise interface for closing the machine theorem once the genuine
implementation is proved to obey the canonical charged ledger. -/
theorem rationalStatementOfLedger {P : Light.Program} {p : Nat}
    {Tn : Nat → Nat → Nat} {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need)
    (hb : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime MachineAdapter.targetExponent := by
  apply MachineAdapter.rationalStatementOfMinPlusExecution hs hn
  intro κ
  obtain ⟨k, C, hC⟩ := hb κ
  let time : Nat → Real := fun n =>
    Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real))
  have htime : ∀ n, 0 ≤ time n := by
    intro n
    unfold time Light.timeUpTo
    positivity
  have hdom : time =O[atTop] AsymptoticCosts.completeCost k := by
    apply IsBigO.of_bound C
    filter_upwards [hC, eventually_ge_atTop (1 : Nat)] with n h hn
    simpa only [Real.norm_of_nonneg (htime n),
      Real.norm_of_nonneg (AsymptoticCosts.completeCostNonnegative k n hn)]
      using h
  have hbound := AsymptoticCosts.costBoundOfDomination time k hdom
  obtain ⟨C', hC'⟩ := isBigO_iff.mp hbound
  refine ⟨C', ?_⟩
  filter_upwards [hC'] with n h
  have hp : 0 ≤ (n : Real) ^ (299294792 / 100000000 : Real) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ht : (MachineAdapter.targetExponent : Real) =
      (299294792 / 100000000 : Real) := by
    norm_num [MachineAdapter.targetExponent]
  simpa only [Real.norm_of_nonneg (htime n), Real.norm_of_nonneg hp, ht]
    using h

#print axioms rationalStatementOfLedger

end ThinMatrix.CanonicalMachineAdapter

