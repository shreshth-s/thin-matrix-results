import CompletedRootProducts

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Precompute actual binary binomial weights once, then shift/filter and
weight every formal degree of every retained cyclic product. All intermediate
weighted cells and the complete cyclic sums are retained. This module does
not identify the family sum with the full LOW contribution. -/
namespace ThinMatrix.WeightedRootProducts
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators

def weightBudget (k t : ℕ) : ℕ := 100*(k+t+2)*BackendScalarBits.scalarUnit (CachedLowQuery.weightBitWidth k t)

def weights (k t : ℕ) : Run (Vector Cell t) :=
  let out := tabulate (Vector.replicate t ()) (fun d =>
    let w := BinaryQueryWeights.weight k t d.val
    ⟨BinaryLowQuery.signedCell w.value,w.operations,w.operations+16⟩)
  ⟨out.value,out.bitSteps,out.control+3*t+4⟩

theorem weights_get (k t : ℕ) (d : Fin t) : view ((weights k t).value.get d)=(TensorContraction.residualWeight k t d.val : ℤ) := by
  simp only [weights,tabulate_get,view,BinaryLowQuery.signedCell_view,BinaryQueryWeights.weight_value,CachedLowQuery.weightCounted_value]

theorem weights_bound (k t : ℕ) (d : Fin t) : (view ((weights k t).value.get d)).natAbs≤2^k := by
  rw [weights_get]
  have h := BinaryLowBounds.residualWeight_bound k t d.val
  exact_mod_cast (show ((TensorContraction.residualWeight k t d.val : ℤ).natAbs:ℤ)≤(2^k:ℕ) by simpa only [Int.natCast_natAbs] using h)

theorem weights_bits (k t : ℕ) : (weights k t).bitSteps≤t*weightBudget k t :=
  tabulate_bits _ _ (fun d => BinaryQueryWeights.weight_cost k t d.val)

theorem weights_control (k t : ℕ) : (weights k t).control≤t*(weightBudget k t+48)+8+3*t+4 := by
  have h := tabulate_control (Vector.replicate t ())
    (fun (d : Fin t) => let w := BinaryQueryWeights.weight k t d.val
      (⟨BinaryLowQuery.signedCell w.value,w.operations,w.operations+16⟩ : Run Cell))
    (fun d => Nat.add_le_add_right (BinaryQueryWeights.weight_cost k t d.val) 16)
  dsimp only at h
  simpa only [weights,weightBudget,Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add_right h (3*t)) 4

def term {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) : Run Cell :=
  if card≤d.val then
    if hf : d.val-card<F then
      let x := mul (ws.get d) ((product.get ⟨d.val-card,hf⟩).get r)
      ⟨x.value,x.bitSteps,16⟩
    else ⟨zero,0,16⟩
  else ⟨zero,0,16⟩

theorem term_value {F q t : ℕ} [NeZero q] (ws : Vector Cell t) (product : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) :
    view (term ws product card d r).value=
      if card≤d.val then view (ws.get d)*((ResidualPolynomialDegree.decode product).coeff (d.val-card)) r else 0 := by
  rw [ResidualPolynomialDegree.decode_coeff]
  unfold term
  split_ifs <;> simp [cellView]

theorem term_bound {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card W A : ℕ)
    (hw : ∀ d, (view (ws.get d)).natAbs≤W) (ha : Bound A product) (d : Fin t) (r : Fin q) :
    (view (term ws product card d r).value).natAbs≤W*A := by
  unfold term
  split_ifs <;> simp only [mul_view,Int.natAbs_mul,zero_view,Int.natAbs_zero]
  · exact Nat.mul_le_mul (hw d) (ha _ _)
  all_goals exact Nat.zero_le _

theorem term_bits {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card W A : ℕ)
    (hw : ∀ d, (view (ws.get d)).natAbs≤W) (ha : Bound A product) (d : Fin t) (r : Fin q) :
    (term ws product card d r).bitSteps≤BackendScalarBits.backendScalarUnit (W+A).size := by
  unfold term
  split_ifs
  · exact mul_price _ _ _ (Nat.size_le_size ((hw d).trans (by omega)))
      (Nat.size_le_size ((ha _ _).trans (by omega)))
  all_goals exact Nat.zero_le _

theorem term_control {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card : ℕ) (d : Fin t) (r : Fin q) :
    (term ws product card d r).control=16 := by unfold term; split_ifs <;> rfl

structure Completed (t q : ℕ) where
  terms : Run (Block t q)
  selector : Vector Bool t
  sum : Run (Vector Cell q)

def execute {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card : ℕ) : Run (Completed t q) :=
  let template := CompletedRootProducts.shape ws.toArray.size q
  let terms := mapBlock (template.value.cast (by simp)) (term ws product card)
  let selector := GroupedPreparation.ofStoredFn ws (fun _ => true)
  let sum := BinaryGroupedCompletion.runRow selector terms.value
  ⟨⟨terms,selector,sum⟩,terms.bitSteps+sum.bitSteps,template.control+terms.control+8*ws.toArray.size+sum.control+16⟩

theorem execute_value {F q t : ℕ} [NeZero q] (ws : Vector Cell t) (product : Block F q) (card : ℕ) (r : Fin q) :
    view ((execute ws product card).value.sum.value.get r)=
      ∑ d : Fin t, if card≤d.val then view (ws.get d)*((ResidualPolynomialDegree.decode product).coeff (d.val-card)) r else 0 := by
  simp only [execute,BinaryGroupedCompletion.runRow_view,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,↓reduceIte]
  change (∑ d : Fin t, cellView (mapBlock _ _).value d r)=_
  simp only [mapBlock_get,term_value]

def bitBudget (t q W A : ℕ) : ℕ :=
  t*(q*BackendScalarBits.backendScalarUnit (W+A).size)+t*(q*BackendScalarBits.backendScalarUnit (t*(W*A)).size)
def controlBudget (t q : ℕ) : ℕ := 3*(t+q)+4+(t*(q*48+40)+8)+8*t+(t*(40*q+24)+3*q+4)+16

theorem execute_bound {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card W A : ℕ)
    (hw : ∀ d, (view (ws.get d)).natAbs≤W) (ha : Bound A product) (r : Fin q) :
    (view ((execute ws product card).value.sum.value.get r)).natAbs≤t*(W*A) := by
  apply BinaryGroupedCompletion.runRow_abs
  intro d r
  change (cellView (mapBlock _ _).value d r).natAbs≤_
  rw [mapBlock_get]
  exact term_bound _ _ _ W A hw ha d r

theorem execute_bits {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card W A : ℕ)
    (hw : ∀ d, (view (ws.get d)).natAbs≤W) (ha : Bound A product) :
    (execute ws product card).bitSteps≤bitBudget t q W A := by
  apply Nat.add_le_add
  · exact mapBlock_bits _ _ (term_bits _ _ _ W A hw ha)
  · apply BinaryGroupedCompletion.runRow_bits (W*A) _ _ _ (le_refl _)
    intro d r
    change (cellView (mapBlock _ _).value d r).natAbs≤_
    rw [mapBlock_get]
    exact term_bound _ _ _ W A hw ha d r

theorem execute_control {F q t : ℕ} (ws : Vector Cell t) (product : Block F q) (card : ℕ) :
    (execute ws product card).control≤controlBudget t q := by
  have ht := mapBlock_control ((CompletedRootProducts.shape ws.toArray.size q).value.cast (by simp : ws.toArray.size=t))
    (term ws product card) (fun d r => (term_control _ _ _ d r).le)
  have hs := BinaryGroupedCompletion.runRow_control (execute ws product card).value.selector (execute ws product card).value.terms.value
  dsimp only [execute,CompletedRootProducts.shape] at ht hs ⊢
  simp only [Vector.size_toArray] at ht hs ⊢
  unfold controlBudget
  norm_num only at ht
  omega

structure Prepared (F q t M : ℕ) where
  products : Vector (Block F q) M
  weights : Run (Vector Cell t)
  outputs : Run (Vector (Completed t q) M)

def prepare {F q M : ℕ} (k t card : ℕ) (products : Vector (Block F q) M) : Run (Prepared F q t M) :=
  let ws := weights k t
  let out := tabulate products (fun i => execute ws.value (products.get i) card)
  ⟨⟨products,ws,out⟩,ws.bitSteps+out.bitSteps,ws.control+out.control+8⟩

theorem prepare_value {F q M : ℕ} [NeZero q] (k t card : ℕ) (products : Vector (Block F q) M)
    (i : Fin M) (r : Fin q) :
    view (((prepare k t card products).value.outputs.value.get i).sum.value.get r)=
      ∑ d : Fin t, if card≤d.val then (TensorContraction.residualWeight k t d.val : ℤ)*
        ((ResidualPolynomialDegree.decode (products.get i)).coeff (d.val-card)) r else 0 := by
  simp only [prepare,tabulate_get,execute_value,weights_get]

theorem prepare_bound {F q M : ℕ} (k t card A : ℕ) (products : Vector (Block F q) M)
    (ha : ∀ i, Bound A (products.get i)) (i : Fin M) (r : Fin q) :
    (view (((prepare k t card products).value.outputs.value.get i).sum.value.get r)).natAbs≤t*(2^k*A) := by
  simp only [prepare,tabulate_get]
  exact execute_bound _ _ _ _ A (weights_bound k t) (ha i) r

theorem prepare_bits {F q M : ℕ} (k t card A : ℕ) (products : Vector (Block F q) M)
    (ha : ∀ i, Bound A (products.get i)) :
    (prepare k t card products).bitSteps≤t*weightBudget k t+M*bitBudget t q (2^k) A :=
  Nat.add_le_add (weights_bits k t) (tabulate_bits _ _ (fun i => execute_bits _ _ _ _ A (weights_bound k t) (ha i)))

theorem prepare_control {F q M : ℕ} (k t card : ℕ) (products : Vector (Block F q) M) :
    (prepare k t card products).control≤t*(weightBudget k t+48)+8+3*t+4+(M*(controlBudget t q+32)+8)+8 :=
  Nat.add_le_add_right (Nat.add_le_add (weights_control k t) (tabulate_control _ _ (fun _ => execute_control _ _ _))) 8

#print axioms weights_get
#print axioms weights_bound
#print axioms weights_bits
#print axioms weights_control
#print axioms term_value
#print axioms term_bound
#print axioms term_bits
#print axioms term_control
#print axioms execute_value
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
#print axioms prepare_value
#print axioms prepare_bound
#print axioms prepare_bits
#print axioms prepare_control
end ThinMatrix.WeightedRootProducts
