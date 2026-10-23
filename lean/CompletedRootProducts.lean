import GraphRootCompletion
import BinaryLowQuery

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Full products of stored completed roots. Reshaping copies binary cells.
The existing exact binary polynomial-dot circuit is run for every output
formal degree and cyclic residue. No fast multiplication or selected-output
cost is substituted. Native loop construction has a separate control charge. -/
namespace ThinMatrix.CompletedRootProducts
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators

def shape (F q : ℕ) : Run (Block F q) :=
  ⟨Vector.replicate F (Vector.replicate q zero),0,3*(F+q)+4⟩

def inflate (F q : ℕ) (row : Vector Cell (F*q)) : Run (Block F q) :=
  let template := shape F q
  let out := mapBlock template.value (fun d r => let x := copy (row.get (finProdFinEquiv (d,r))); ⟨x.value,x.bitSteps,8⟩)
  ⟨out.value,out.bitSteps,template.control+out.control+8⟩

theorem inflate_value (F q : ℕ) (row : Vector Cell (F*q)) (d : Fin F) (r : Fin q) :
    cellView (inflate F q row).value d r=view (row.get (finProdFinEquiv (d,r))) := by
  simp only [inflate,mapBlock_get,copy_view]

theorem inflate_bound (F q A : ℕ) (row : Vector Cell (F*q))
    (ha : ∀ c, (view (row.get c)).natAbs≤A) : Bound A (inflate F q row).value := by
  intro d r
  rw [inflate_value]
  exact ha _

theorem inflate_bits (F q A : ℕ) (row : Vector Cell (F*q))
    (ha : ∀ c, (view (row.get c)).natAbs≤A) :
    (inflate F q row).bitSteps≤F*(q*BackendScalarBits.backendScalarUnit A.size) :=
  mapBlock_bits _ _ (fun _ _ => copy_price _ _ (Nat.size_le_size (ha _)))

def inflateControl (F q : ℕ) : ℕ := 3*(F+q)+4+(F*(q*40+40)+8)+8

theorem inflate_control (F q : ℕ) (row : Vector Cell (F*q)) :
    (inflate F q row).control≤ inflateControl F q :=
  Nat.add_le_add_right (Nat.add_le_add_left (mapBlock_control _ _ (fun _ _ => le_refl 8)) _) 8

theorem dense_bound {F q : ℕ} (a : Block F q) (A : ℕ) (ha : Bound A a) :
    ∀ d r, |SparseLocalForms.denseRead (BinaryLowQuery.blockView a) d r|≤(A:ℤ) := by
  intro d r
  simpa only [SparseLocalForms.denseRead,BinaryLowQuery.blockView,Vector.get_map,cellView,view,← Int.natCast_natAbs] using
    (Int.ofNat_le.mpr (ha d r))

theorem read_decode {F q : ℕ} [NeZero q] (a : Block F q) (n : ℕ) (r : Fin q) :
    CachedLowQuery.blockCoeff (BinaryLowQuery.blockView a) n r=((ResidualPolynomialDegree.decode a).coeff n) r := by
  rw [ResidualPolynomialDegree.decode_coeff]
  simp only [CachedLowQuery.blockCoeff,BinaryLowQuery.blockView,Vector.get_map,cellView,view]

theorem dot_decode {F q : ℕ} [NeZero q] (a b : Block F q) (n : ℕ) (r : Fin q) :
    BitArraySimulation.denote (BinaryLowQuery.polynomialDot a b n r).value=
      ((ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b).coeff n) r := by
  rw [BinaryLowQuery.polynomialDot_value]
  unfold CachedLowQuery.polynomialDot
  simp only [List.map_map,Function.comp_def,CachedLowQuery.selectedDot_value]
  rw [Polynomial.coeff_mul,CyclicRing.sum_coeff,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← List.sum_toFinset _ (List.nodup_range (n:=n+1))]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro d _
  have hl : CachedLowQuery.blockCoeff (BinaryLowQuery.blockView a) d=(ResidualPolynomialDegree.decode a).coeff d := funext (read_decode a d)
  have hr : CachedLowQuery.blockCoeff (BinaryLowQuery.blockView b) (n-d)=(ResidualPolynomialDegree.decode b).coeff (n-d) := funext (read_decode b (n-d))
  rw [hl,hr]

theorem decode_degree {F q : ℕ} [NeZero q] (a : Block F q) :
    (ResidualPolynomialDegree.decode a).natDegree≤F-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d _
  exact (Polynomial.natDegree_monomial_le _).trans (by have := d.isLt; omega)

def outputLength (F : ℕ) : ℕ := 2*F-1

def execute {F q : ℕ} [NeZero q] (a b : Block F q) : Run (Block (outputLength F) q) :=
  let template := shape (outputLength a.toArray.size) q
  let out := mapBlock (template.value.cast (by simp)) (fun d r =>
    let dot := BinaryLowQuery.polynomialDot a b d.val r
    ⟨BinaryLowQuery.signedCell dot.value,dot.operations,8*(d.val+1)*(q+1)+8⟩)
  ⟨out.value,out.bitSteps,template.control+out.control+8⟩

theorem execute_coeff {F q : ℕ} [NeZero q] (a b : Block F q) (d : Fin (outputLength F)) (r : Fin q) :
    cellView (execute a b).value d r=((ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b).coeff d.val) r := by
  simp only [execute,mapBlock_get]
  exact dot_decode a b d.val r

theorem execute_polynomial {F q : ℕ} [NeZero q] (a b : Block F q) :
    ResidualPolynomialDegree.decode (execute a b).value=ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b := by
  apply Polynomial.ext
  intro n
  funext r
  rw [ResidualPolynomialDegree.decode_coeff]
  split
  · exact execute_coeff _ _ _ _
  · rename_i hn
    by_cases hF : F=0
    · subst F
      simp [ResidualPolynomialDegree.decode]
    · have hd := Polynomial.natDegree_mul_le (p:=ResidualPolynomialDegree.decode a) (q:=ResidualPolynomialDegree.decode b)
      have ha := decode_degree a
      have hb := decode_degree b
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show (ResidualPolynomialDegree.decode a*ResidualPolynomialDegree.decode b).natDegree<n by
        unfold outputLength at hn
        omega)]
      rfl

def width (q N A : ℕ) : ℕ :=
  A.size+(A^2).size+(q*A^2).size+((N+1)*(q*A^2)).size+N.size+q.size+1

theorem dot_bits {F q : ℕ} [NeZero q] (a b : Block F q) (N A d : ℕ)
    (ha : Bound A a) (hb : Bound A b) (hd : d≤N) (r : Fin q) :
    (BinaryLowQuery.polynomialDot a b d r).operations≤600*(N+1)*q*(width q N A+1)^2 := by
  have hds : d.size≤N.size := Nat.size_le_size hd
  have hp : ((d+1)*(q*A^2)).size≤((N+1)*(q*A^2)).size := Nat.size_le_size (Nat.mul_le_mul_right _ (by omega))
  have h := BinaryLowQuery.polynomialDot_cost_of_selectedCost a b A d (width q N A)
    (dense_bound a A ha) (dense_bound b A hb) (by unfold width; omega) (by unfold width; omega)
    (by unfold width; omega) r (by
      intro e he
      have hed : e≤d := by have := List.mem_range.mp he; omega
      have hes := Nat.size_le_size (hed.trans hd)
      have hrs := Nat.size_le_size ((Nat.sub_le d e).trans hd)
      exact BinaryLowQuery.selectedDot_cost_probe a b A (width q N A) e (d-e) r ha hb
        (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
        (by unfold width; omega) (by unfold width; omega) (by unfold width; omega))
  exact h.trans (by gcongr)

def magnitude (F q A : ℕ) : ℕ := (outputLength F+1)*q*A^2

theorem execute_bound {F q : ℕ} [NeZero q] (a b : Block F q) (A : ℕ)
    (ha : Bound A a) (hb : Bound A b) : Bound (magnitude F q A) (execute a b).value := by
  intro d r
  have h := BinaryLowBounds.polynomialDot_bound (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) A d.val
    (dense_bound a A ha) (dense_bound b A hb) r
  have hz : cellView (execute a b).value d r=(CachedLowQuery.polynomialDot (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) d.val r).1 := by
    simp only [execute,mapBlock_get,view,BinaryLowQuery.signedCell_view,BinaryLowQuery.polynomialDot_value]
  rw [hz]
  have hn : (CachedLowQuery.polynomialDot (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) d.val r).1.natAbs≤(d.val+1)*q*A^2 := by
    exact_mod_cast (show ((CachedLowQuery.polynomialDot (BinaryLowQuery.blockView a) (BinaryLowQuery.blockView b) d.val r).1.natAbs:ℤ)≤((d.val+1)*q*A^2:ℕ) by simpa only [Int.natCast_natAbs] using h)
  exact hn.trans (by unfold magnitude; gcongr; exact Nat.le_of_lt d.isLt)

def bitBudget (F q A : ℕ) : ℕ := outputLength F*(q*(600*(outputLength F+1)*q*(width q (outputLength F) A+1)^2))
def controlBudget (F q : ℕ) : ℕ := 3*(outputLength F+q)+4+
  (outputLength F*(q*(8*(outputLength F+1)*(q+1)+8+32)+40)+8)+8

theorem execute_bits {F q : ℕ} [NeZero q] (a b : Block F q) (A : ℕ)
    (ha : Bound A a) (hb : Bound A b) : (execute a b).bitSteps≤bitBudget F q A := by
  apply mapBlock_bits
  intro d r
  exact dot_bits a b _ A d.val ha hb (Nat.le_of_lt d.isLt) r

theorem execute_control {F q : ℕ} [NeZero q] (a b : Block F q) :
    (execute a b).control≤controlBudget F q := by
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · simp [shape]
  · apply mapBlock_control
    intro d _
    change 8*(d.val+1)*(q+1)+8 ≤ _
    gcongr
    exact Nat.le_of_lt d.isLt

noncomputable def polynomialOf {F q : ℕ} [NeZero q] (f : Fin F → Fin q → ℤ) : Polynomial (CyclicRing.Cyclic q) :=
  ∑ d : Fin F, Polynomial.monomial d.val (f d)

theorem polynomialOf_coeff {F q : ℕ} [NeZero q] (f : Fin F → Fin q → ℤ) (n : ℕ) (r : Fin q) :
    ((polynomialOf f).coeff n) r=if h : n<F then f ⟨n,h⟩ r else 0 := by
  classical
  simp only [polynomialOf,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,CyclicRing.sum_coeff]
  by_cases hn : n<F
  · rw [Finset.sum_eq_single ⟨n,hn⟩]
    · simp [hn]
    · intro i _ hi
      have hv : i.val≠n := by intro h; exact hi (Fin.ext h)
      simp [hv]
    · simp
  · have hz (d : Fin F) : d.val≠n := by intro h; have := d.isLt; omega
    simp [hn,hz]

#print axioms polynomialOf_coeff

#print axioms inflate_value
#print axioms inflate_bound
#print axioms inflate_bits
#print axioms inflate_control
#print axioms dense_bound
#print axioms read_decode
#print axioms dot_decode
#print axioms decode_degree
#print axioms execute_coeff
#print axioms execute_polynomial
#print axioms dot_bits
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.CompletedRootProducts
