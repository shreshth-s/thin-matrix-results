import Std
import Init.Grind.Ordered.Rat

/-!
# Limited exact arithmetic certificate for the aligned witness

This file proves exact witness identities and independently evaluates the 47
cost inequalities over compact rational boxes for T, G, q1. The relations
q2=q1+2*theta, Esource=T+q1, Ebox=T-G are encoded in the affine formulas.

ANALYTIC SCOPE: this file does not define real logarithms or entropy. It does
not prove that these boxes enclose the real expressions in the research note.
The boxes were outward rounded from the Python rational interval computation;
their relationship to real logarithms is proved separately in
`RealCertificate.lean` and is not an assumption hidden in this file.
No theorem here establishes the embedding/cache lemmas or an APSP algorithm.

Uses kernel reduction (decide +kernel) and proof-producing grind; no sorry,
native_decide, custom axiom, or external package.
-/
namespace ThinMatrix.AlignedCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def c : Rat := 1066550171 / 100000000
def theta : Rat := 652978214 / 10000000000
def b : Rat := 46046346 / 1000000000
def delta : Rat := 705208 / 100000000
def R : Nat := 1000000000
def S : Nat := 768979045
def eta : Rat := b / (R : Rat)
def u : Rat := (S : Rat) * eta
def v : Rat := ((R - S : Nat) : Rat) * eta
def e : Rat := b + u

theorem witnessIdentities :
    eta = 46046346 / 1000000000000000000 ∧
    u = 3540867517281957 / 100000000000000000 ∧
    v = 1063767082718043 / 100000000000000000 ∧
    e = 8145502117281957 / 100000000000000000 ∧
    u + v = b ∧ (R : Rat) * eta = b ∧ (S : Rat) * eta = u ∧
    3 - delta = 299294792 / 100000000 := by
  decide +kernel

-- The real-log/entropy interpretation of these compact boxes is NOT proved here.
def tLo : Rat := 12059362922115430 / 1000000000000000
def tHi : Rat := 12059362922115431 / 1000000000000000
def gLo : Rat := 86576385178389 / 1000000000000000
def gHi : Rat := 86576385178390 / 1000000000000000
def qLo : Rat := 348125793364647 / 1000000000000000
def qHi : Rat := 348125793364648 / 1000000000000000

theorem boxesOrdered : tLo ≤ tHi ∧ gLo ≤ gHi ∧ qLo ≤ qHi := by
  decide +kernel

structure Affine where
  constant : Rat
  tCoeff : Rat
  gCoeff : Rat
  qCoeff : Rat

def eval (a : Affine) (T G q1 : Rat) : Rat :=
  a.constant + a.tCoeff*T + a.gCoeff*G + a.qCoeff*q1

def signedLower (coefficient lo hi : Rat) : Rat :=
  if 0 ≤ coefficient then coefficient*lo else coefficient*hi

def lower (a : Affine) : Rat :=
  a.constant + signedLower a.tCoeff tLo tHi +
    signedLower a.gCoeff gLo gHi + signedLower a.qCoeff qLo qHi

theorem signedLower_le (coefficient lo hi x : Rat)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    signedLower coefficient lo hi ≤ coefficient*x := by
  unfold signedLower
  split
  next h => exact Rat.mul_le_mul_of_nonneg_left hlo h
  next h =>
    have hn : 0 ≤ -coefficient := by grind
    have hm := Rat.mul_le_mul_of_nonneg_left hhi hn
    have hh := Rat.neg_le_neg hm
    simpa only [Rat.neg_mul, Rat.neg_neg] using hh

theorem lower_le_eval (a : Affine) (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi)
    (hq : qLo ≤ q1 ∧ q1 ≤ qHi) : lower a ≤ eval a T G q1 := by
  have ht := signedLower_le a.tCoeff tLo tHi T hT.1 hT.2
  have hg := signedLower_le a.gCoeff gLo gHi G hG.1 hG.2
  have hq' := signedLower_le a.qCoeff qLo qHi q1 hq.1 hq.2
  unfold lower eval
  grind

structure Check where
  label : String
  target : Rat
  expression : Affine

def regimes : List Check := [
  ⟨"ordinary tail regime", 0, ⟨c-5, 0, 0, 0⟩⟩,
  ⟨"positive switching threshold", 0, ⟨theta, 0, 0, 0⟩⟩,
  ⟨"unweighted cache cutoff increasing", 0, ⟨1/2-theta, 0, 0, 0⟩⟩,
  ⟨"stored cutoff increasing", 0, ⟨4/5-theta, 0, 0, 0⟩⟩,
  ⟨"ordinary private-cap tail geometric", 0, ⟨1-4/(c-1), 0, 0, 0⟩⟩,
  ⟨"box private-cap tail geometric", 0, ⟨1-4*(1-theta)/(c-1+theta), 0, 0, 0⟩⟩,
  ⟨"positive box gain", 0, ⟨0, 0, 1, 0⟩⟩,
  ⟨"box gain below one", 0, ⟨1, 0, -1, 0⟩⟩,
  ⟨"positive residual query exponent", 0, ⟨0, 0, 0, 1⟩⟩,
  ⟨"positive stored query exponent", 0, ⟨2*theta, 0, 0, 1⟩⟩,
  ⟨"positive source encoder slope", 0, ⟨1/2, 1, 0, 1⟩⟩,
  ⟨"positive box encoder slope", 0, ⟨1/2, 1, -1, 0⟩⟩,
  ⟨"positive original geometry slope", 0, ⟨-1/2, 1, 0, 0⟩⟩,
  ⟨"positive frozen-factor count", 0, ⟨(S : Rat), 0, 0, 0⟩⟩,
  ⟨"at least two cyclic factors", 1, ⟨((R-S : Nat) : Rat), 0, 0, 0⟩⟩,
  ⟨"positive final ring exponent", 0, ⟨v, 0, 0, 0⟩⟩,
  ⟨"positive candidate exponent", 0, ⟨eta, 0, 0, 0⟩⟩,
  ⟨"middle blocks fit", 0, ⟨1-b, 0, 0, 0⟩⟩,
  ⟨"incidence bookkeeping after enumeration", delta, ⟨b-eta, 0, 0, 0⟩⟩
]

/-- Phase I costs after substituting q2 and both E's; ep=b+x. -/
def scalarPhase (x : Rat) (endpoint : String) : List Check :=
  let ep := b+x
  [⟨"phase I "++endpoint++": boxes", delta, ⟨b-x-eta, 0, ep, 0⟩⟩,
   ⟨"phase I "++endpoint++": residual queries", delta, ⟨b-eta, 0, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": stored queries", delta, ⟨b-eta-ep*(2*theta), 0, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": cache encodings", delta, ⟨1+b-x/2-eta, -ep, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": ordinary box encodings", delta, ⟨1+b-x/2-eta, -ep, ep, 0⟩⟩,
   ⟨"phase I "++endpoint++": matrix formation", delta, ⟨1-3*x/2-eta, 0, 0, 0⟩⟩,
   ⟨"phase I "++endpoint++": original tile geometry", 0, ⟨1+x/2, -ep, 0, 0⟩⟩]

/-- Cyclic preprocessing/residual costs pay z; stored lookup costs do not. -/
def cyclicPhase (z : Rat) (endpoint : String) : List Check :=
  [⟨"phase II "++endpoint++": boxes", delta, ⟨b-u-z-eta, 0, e, 0⟩⟩,
   ⟨"phase II "++endpoint++": residual queries", delta, ⟨b-z-eta, 0, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": stored queries", delta, ⟨b-eta-e*(2*theta), 0, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": cache encodings", delta, ⟨1+b-u/2-z-eta, -e, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": ordinary box encodings", delta, ⟨1+b-u/2-z-eta, -e, e, 0⟩⟩,
   ⟨"phase II "++endpoint++": matrix formation", delta, ⟨1-3*u/2-z-eta, 0, 0, 0⟩⟩,
   ⟨"phase II "++endpoint++": original tile geometry", 0, ⟨1+u/2, -e, 0, 0⟩⟩]

/-- Unexpanded phase-I expressions, in the same order as the Python verifier.
This second representation makes the substitutions and affine expansion auditable.
-/
def scalarCosts (x T G q1 : Rat) : List Rat :=
  let ep := b+x
  let q2 := q1+2*theta
  let Esource := T+q1
  let Ebox := T-G
  [b-x+ep*G-eta,
   b-ep*q1-eta,
   b-ep*q2-eta,
   1+b-x/2-ep*Esource-eta,
   1+b-x/2-ep*Ebox-eta,
   1-3*x/2-eta,
   1+x/2-ep*T]

/-- Unexpanded cyclic-phase expressions. The cyclic exponent z is charged
in both encoders and in residual queries; it is absent from stored lookups.
-/
def cyclicCosts (z T G q1 : Rat) : List Rat :=
  let q2 := q1+2*theta
  let Esource := T+q1
  let Ebox := T-G
  [b-u-z+e*G-eta,
   b-z-e*q1-eta,
   b-e*q2-eta,
   1+b-u/2-z-e*Esource-eta,
   1+b-u/2-z-e*Ebox-eta,
   1-3*u/2-z-eta,
   1+u/2-e*T]

theorem scalarPhaseEval (x T G q1 : Rat) (endpoint : String) :
    (scalarPhase x endpoint).map (fun check => eval check.expression T G q1) =
      scalarCosts x T G q1 := by
  simp only [scalarPhase, scalarCosts, eval, List.map_cons, List.map_nil, List.cons.injEq]
  grind

theorem cyclicPhaseEval (z T G q1 : Rat) (endpoint : String) :
    (cyclicPhase z endpoint).map (fun check => eval check.expression T G q1) =
      cyclicCosts z T G q1 := by
  simp only [cyclicPhase, cyclicCosts, eval, List.map_cons, List.map_nil, List.cons.injEq]
  grind

def checks : List Check :=
  regimes ++ scalarPhase 0 "initial" ++ scalarPhase u "freeze" ++
    cyclicPhase 0 "start" ++ cyclicPhase v "final"

theorem checkCount : checks.length = 47 := by decide +kernel

/-- Kernel recomputation from witness constants and three parameter boxes.
No Python-generated per-cost lower endpoints are imported. -/
theorem numericalMargins :
    checks.all (fun check => decide (check.target < lower check.expression)) = true := by
  decide +kernel

/-- Conditional interval-to-cost theorem. Only three rational enclosure pairs
are assumed. This theorem does not assert a real-log enclosure. -/
theorem allCostsOfEnclosures (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi)
    (hq : qLo ≤ q1 ∧ q1 ≤ qHi) :
    ∀ check ∈ checks, check.target < eval check.expression T G q1 := by
  intro check hmember
  have hb : decide (check.target < lower check.expression) = true :=
    (List.all_eq_true.mp numericalMargins) check hmember
  have hm : check.target < lower check.expression := of_decide_eq_true hb
  have hl := lower_le_eval check.expression T G q1 hT hG hq
  grind

#print axioms witnessIdentities
#print axioms scalarPhaseEval
#print axioms cyclicPhaseEval
#print axioms checkCount
#print axioms numericalMargins
#print axioms allCostsOfEnclosures
end ThinMatrix.AlignedCertificate
