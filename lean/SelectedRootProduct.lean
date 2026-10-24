import WeightedRootProducts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Evaluate one requested cyclic coefficient of the complete weighted root
product. Every dot reads all cyclic entries of both retained roots. The formal
degree/channel weights are summed before the caller's exact normalization.
No individual term is divided. This removes the unused all-residue product
output from the finite correctness implementation and retains its O(q) dot
work per formal degree. -/
namespace ThinMatrix.SelectedRootProduct
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators
variable {F q t : ℕ} [NeZero q]

def term (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) : Run Cell :=
  if card≤d.val then
    let dot := BinaryLowQuery.polynomialDot a b (d.val-card) r
    let prod := mul (ws.get d) (BinaryLowQuery.signedCell dot.value)
    ⟨prod.value,dot.operations+prod.bitSteps,8*(d.val+1)*(q+1)+32⟩
  else ⟨zero,0,16⟩

theorem term_value (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) :
    view (term ws a b card d r).value=
      if card≤d.val then view (ws.get d)*((ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b).coeff (d.val-card)) r else 0 := by
  unfold term
  split_ifs
  · rw [mul_view]
    exact congrArg (fun z : ℤ => view (ws.get d)*z) (CompletedRootProducts.dot_decode a b (d.val-card) r)
  · rfl

def productMagnitude (q t A : ℕ) : ℕ := (t+1)*q*A^2

theorem dot_bound (a b : Block F q) (d A : ℕ) (ha : Bound A a) (hb : Bound A b)
    (hd : d≤t) (r : Fin q) :
    (view (BinaryLowQuery.signedCell (BinaryLowQuery.polynomialDot a b d r).value)).natAbs≤productMagnitude q t A := by
  simp only [view,BinaryLowQuery.signedCell_view,BinaryLowQuery.polynomialDot_value]
  have hh := BinaryLowBounds.polynomialDot_bound (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) A d
    (CompletedRootProducts.dense_bound a A ha) (CompletedRootProducts.dense_bound b A hb) r
  have hnat : (CachedLowQuery.polynomialDot (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) d r).1.natAbs≤(d+1)*q*A^2 := by
    exact_mod_cast (show ((CachedLowQuery.polynomialDot (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) d r).1.natAbs:ℤ)≤((d+1)*q*A^2:ℕ) by simpa only [Int.natCast_natAbs] using hh)
  exact hnat.trans (by unfold productMagnitude; gcongr)

theorem term_bound (ws : Vector Cell t) (a b : Block F q) (card W A : ℕ)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : Bound A a) (hb : Bound A b) (d : Fin t) (r : Fin q) :
    (view (term ws a b card d r).value).natAbs≤W*productMagnitude q t A := by
  unfold term
  split_ifs
  · rw [mul_view,Int.natAbs_mul]
    exact Nat.mul_le_mul (hw d) (dot_bound (t:=t) a b (d.val-card) A ha hb (by omega) r)
  · simp only [zero_view,Int.natAbs_zero,Nat.zero_le]

def termBudget (q t W A : ℕ) : ℕ :=
  600*(t+1)*q*(CompletedRootProducts.width q t A+1)^2+
    BackendScalarBits.backendScalarUnit (W+productMagnitude q t A).size

theorem term_bits (ws : Vector Cell t) (a b : Block F q) (card W A : ℕ)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : Bound A a) (hb : Bound A b) (d : Fin t) (r : Fin q) :
    (term ws a b card d r).bitSteps≤termBudget q t W A := by
  unfold term
  split_ifs
  · apply Nat.add_le_add
    · exact CompletedRootProducts.dot_bits a b t A (d.val-card) ha hb (by omega) r
    · apply mul_price
      · exact Nat.size_le_size ((hw d).trans (by omega))
      · exact Nat.size_le_size ((dot_bound (t:=t) a b (d.val-card) A ha hb (by omega) r).trans (by omega))
  · exact Nat.zero_le _

theorem term_control (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) :
    (term ws a b card d r).control≤8*(t+1)*(q+1)+32 := by
  unfold term
  split_ifs <;> have := d.isLt <;> nlinarith

def execute (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (r : Fin q) : Run Cell :=
  let terms := tabulate ws (fun d =>
    let x := term ws a b card d r
    (⟨Vector.replicate 1 x.value,x.bitSteps,x.control+8⟩ : Run (Vector Cell 1)))
  let selected := Vector.replicate t true
  let out := BinaryGroupedCompletion.runRow selected terms.value
  ⟨out.value.get 0,terms.bitSteps+out.bitSteps,terms.control+out.control+3*t+16⟩

theorem execute_value (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (r : Fin q) :
    view (execute ws a b card r).value=
      ∑ d : Fin t, if card≤d.val then view (ws.get d)*((ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b).coeff (d.val-card)) r else 0 := by
  simp only [execute,BinaryGroupedCompletion.runRow_view,Vector.get_replicate,↓reduceIte,tabulate_get,term_value]

theorem agrees (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (r : Fin q) :
    view (execute ws a b card r).value=
      view ((WeightedRootProducts.execute ws (CompletedRootProducts.execute a b).value card).value.sum.value.get r) := by
  rw [execute_value,WeightedRootProducts.execute_value,CompletedRootProducts.execute_polynomial]

def bitBudget (q t W A : ℕ) : ℕ :=
  t*termBudget q t W A+t*BackendScalarBits.backendScalarUnit (t*(W*productMagnitude q t A)).size

theorem execute_bound (ws : Vector Cell t) (a b : Block F q) (card W A : ℕ)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : Bound A a) (hb : Bound A b) (r : Fin q) :
    (view (execute ws a b card r).value).natAbs≤t*(W*productMagnitude q t A) := by
  apply BinaryGroupedCompletion.runRow_abs
  intro d c
  simp only [tabulate_get,Vector.get_replicate]
  exact term_bound ws a b card W A hw ha hb d r

theorem execute_bits (ws : Vector Cell t) (a b : Block F q) (card W A : ℕ)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : Bound A a) (hb : Bound A b) (r : Fin q) :
    (execute ws a b card r).bitSteps≤bitBudget q t W A := by
  apply Nat.add_le_add
  · exact tabulate_bits _ _ (fun d => term_bits ws a b card W A hw ha hb d r)
  · have hh := BinaryGroupedCompletion.runRow_bits (W*productMagnitude q t A) (t*(W*productMagnitude q t A)).size
      (Vector.replicate t true)
      (tabulate ws (fun d => let x := term ws a b card d r
        (⟨Vector.replicate 1 x.value,x.bitSteps,x.control+8⟩ : Run (Vector Cell 1)))).value
      (le_refl _)
      (fun d c => by simpa only [tabulate_get,Vector.get_replicate] using term_bound ws a b card W A hw ha hb d r)
    simpa only [Nat.one_mul] using hh

def controlBudget (q t : ℕ) : ℕ := t*(8*(t+1)*(q+1)+72)+8+(64*t+7)+3*t+16

theorem execute_control (ws : Vector Cell t) (a b : Block F q) (card : ℕ) (r : Fin q) :
    (execute ws a b card r).control≤controlBudget q t := by
  have ht := tabulate_control ws (fun d => let x := term ws a b card d r
    (⟨Vector.replicate 1 x.value,x.bitSteps,x.control+8⟩ : Run (Vector Cell 1)))
    (fun d => Nat.add_le_add_right (term_control ws a b card d r) 8)
  have hs := BinaryGroupedCompletion.runRow_control (Vector.replicate t true)
    (tabulate ws (fun d => let x := term ws a b card d r
      (⟨Vector.replicate 1 x.value,x.bitSteps,x.control+8⟩ : Run (Vector Cell 1)))).value
  dsimp only [execute]
  unfold controlBudget
  dsimp only at ht hs
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht hs ⊢
  omega

#print axioms execute_control

#print axioms term_value
#print axioms dot_bound
#print axioms term_bound
#print axioms term_bits
#print axioms term_control
#print axioms execute_value
#print axioms agrees
#print axioms execute_bound
#print axioms execute_bits
end ThinMatrix.SelectedRootProduct
