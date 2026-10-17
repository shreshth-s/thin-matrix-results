import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host
import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
import ThreeSumApsp.RunningTimes.FromClaims.Bounds
import ThreeSumApsp.Statements.Exponents

/-!
# Adapter from actual min-plus executions to the upstream word RAM

These are composition lemmas. They do not supply an improved min-plus program.
The input contract `Light.Solves` contains actual bounded `Light.Exec` runs,
memory framing and append stability. The time hypothesis bounds those runs;
it is not inferred from functional correctness or an abstract operation count.
The upstream host appends four finite procedures and the compiler produces
one fixed RAM program for each fixed input-magnitude exponent.
-/

namespace ThinMatrix.MachineAdapter

open Filter
open ThreeSumApsp ThreeSumApsp.WordRam

def targetExponent : Rat := 299294792 / 100000000

/-- Reuse the actual repeated-squaring controller, preserving its exact costs. -/
theorem appendAPSP {P : Light.Program} {p : Nat} {Tn : Nat → Nat → Nat}
    {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need) :
    ∃ (R : Light.Program) (p' : Nat),
      Light.Solves Light.apTask (P ++ R) p'
        (Light.Sec3.apTime Tn) (Light.Sec3.apNeed need) ∧
      Light.PolyNeed (Light.Sec3.apNeed need) := by
  obtain ⟨R, p', h⟩ := Light.Sec3.isHost_ap.1 P p Tn need hs
  exact ⟨R, p', h, Light.Sec3.isHost_ap.2 need hn⟩

/-- The source-level min-plus solver gives one compiled, correctly laid out
APSP RAM program. The bound is the exact host time, lifted uniformly in U. -/
theorem realizedFromMinPlus {P : Light.Program} {p : Nat}
    {Tn : Nat → Nat → Nat} {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need) :
    Realized EndStatement.APSP (Light.timeUpTo (Light.Sec3.apTime Tn)) := by
  obtain ⟨R, p', h, hneed⟩ := appendAPSP hs hn
  exact Light.Sec3.realized_apsp _ (h.solvedIn hneed)

/-- Final statement conversion, conditional on an actual execution proof and
a bound for its exact host time. No improved solver is postulated or supplied
by this theorem. In particular the time bound includes the host calls at 3nU. -/
theorem rationalStatementOfMinPlusExecution {P : Light.Program} {p : Nat}
    {Tn : Nat → Nat → Nat} {need : Nat → Nat → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need)
    (hb : ∀ κ : Nat, ∃ C : Real, ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
      C * (n : Real) ^ (targetExponent : Real)) :
    EndStatement.APSP.SolvedInTime targetExponent := by
  apply ThreeSumApsp.WordRam.SolvedInTime.endStatement
    (a := (targetExponent : Real)) ?_ rfl
      (by norm_num [targetExponent])
  intro κ
  obtain ⟨C, hC⟩ := hb κ
  exact ThreeSumApsp.FromClaims.solvedAt_of_realized _
    κ (realizedFromMinPlus hs hn) (C := C)
      (by simpa only [pow_zero, mul_one] using hC)

#print axioms appendAPSP
#print axioms realizedFromMinPlus
#print axioms rationalStatementOfMinPlusExecution

end ThinMatrix.MachineAdapter

