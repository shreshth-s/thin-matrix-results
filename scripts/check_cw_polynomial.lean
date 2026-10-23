import CWPolynomialCertificate

/-! Bounded executable checks, independent of the proof expansion. All entries
are exact rationals. These tests run scalar term data, not mathlib's
noncomputable polynomial representation or a rectangular multiplier. -/
open ThinMatrix ThinMatrix.FiniteTrilinear ThinMatrix.CWPolynomialCertificate

private def label {q : Nat} : Axis q → Nat
  | none => 0
  | some none => q+1
  | some (some i) => i.val+1

private def bit (p : Bool) : ℚ := if p then 1 else 0

private def entry (q x y z : Nat) (t : ℚ) : ℚ := Id.run do
  let privateLabel := fun a => 1 ≤ a && a ≤ q
  let corner := bit ((x == q+1 && y == 0 && z == 0) ||
    (x == 0 && y == q+1 && z == 0) || (x == 0 && y == 0 && z == q+1))
  let paired := bit (x == 0 && privateLabel y && y == z) +
    bit (y == 0 && privateLabel x && x == z) +
    bit (z == 0 && privateLabel x && x == y)
  let allSame := bit (privateLabel x && x == y && y == z)
  let loosePairs := bit (x == 0 && privateLabel y && privateLabel z) +
    bit (y == 0 && privateLabel x && privateLabel z) +
    bit (z == 0 && privateLabel x && privateLabel y)
  let allPrivate := bit (privateLabel x && privateLabel y && privateLabel z)
  let terminalPairs := bit (x == 0 && y == q+1 && z == q+1) +
    bit (y == 0 && x == q+1 && z == q+1) +
    bit (z == 0 && x == q+1 && y == q+1)
  let allTerminal := bit (x == q+1 && y == q+1 && z == q+1)
  return t^3*(paired+corner) + t^4*(allSame-loosePairs-q*corner) +
    t^6*(-allPrivate+terminalPairs) - t^7*(q*terminalPairs) +
    t^9*allTerminal-t^10*(q*allTerminal)

private def check (q : Nat) : IO Unit := do
  let axes : List (Axis q) := none :: some none :: List.ofFn (fun i : Fin q => some (some i))
  let mut count := 0
  for t in ([-2, 0, 1, 2] : List ℚ) do
    for i in axes do
      for j in axes do
        for k in axes do
          let actual := total (termsAt q t) i j k
          let expected := entry q (label i) (label j) (label k) t
          unless actual == expected do
            throw (IO.userError s!"CW specialization mismatch q={q}, t={t}, labels={label i},{label j},{label k}")
          count := count+1
  IO.println s!"PASS: q={q}: {count} exact rational scalar entries agree with independent label formula."

def main : IO Unit := do
  for q in [0, 1, 2, 3, 16] do
    check q
  IO.println "PASS: CW scalar terms executed; polynomial coefficients and tensor-power scope are kernel-checked separately."
