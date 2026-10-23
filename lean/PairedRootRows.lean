import CompletedRootProducts
import RootRequestSelection

set_option autoImplicit false

/-! Retained selected root rows to complete paired polynomial products. Every
request position is kept, including duplicates and already zeroed unmatched
rows. Both reshaping copies and every product coefficient are charged. -/
namespace ThinMatrix.PairedRootRows
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial

structure Prepared (F q M : ℕ) where
  left : Run (Vector (Block F q) M)
  right : Run (Vector (Block F q) M)
  products : Run (Vector (Block (CompletedRootProducts.outputLength F) q) M)

def execute {F q M : ℕ} [NeZero q] (left right : Vector (RootRequestSelection.Selected (F*q)) M) :
    Run (Prepared F q M) :=
  let a := tabulate left (fun i => CompletedRootProducts.inflate F q (left.get i).output)
  let b := tabulate right (fun i => CompletedRootProducts.inflate F q (right.get i).output)
  let products := tabulate a.value (fun i => CompletedRootProducts.execute (a.value.get i) (b.value.get i))
  ⟨⟨a,b,products⟩,a.bitSteps+b.bitSteps+products.bitSteps,a.control+b.control+products.control+16⟩

theorem execute_polynomial {F q M : ℕ} [NeZero q] (left right : Vector (RootRequestSelection.Selected (F*q)) M)
    (i : Fin M) :
    ResidualPolynomialDegree.decode ((execute left right).value.products.value.get i)=
      ResidualPolynomialDegree.decode (CompletedRootProducts.inflate F q (left.get i).output).value*
        ResidualPolynomialDegree.decode (CompletedRootProducts.inflate F q (right.get i).output).value := by
  simp only [execute,tabulate_get,CompletedRootProducts.execute_polynomial]

def BoundRows {F q M : ℕ} (A : ℕ) (rows : Vector (RootRequestSelection.Selected (F*q)) M) : Prop :=
  ∀ i c, (view ((rows.get i).output.get c)).natAbs≤A

theorem execute_bound {F q M : ℕ} [NeZero q] (left right : Vector (RootRequestSelection.Selected (F*q)) M)
    (A : ℕ) (ha : BoundRows A left) (hb : BoundRows A right) (i : Fin M) :
    Bound (CompletedRootProducts.magnitude F q A) ((execute left right).value.products.value.get i) := by
  simp only [execute,tabulate_get]
  exact CompletedRootProducts.execute_bound _ _ A
    (CompletedRootProducts.inflate_bound _ _ A _ (ha i)) (CompletedRootProducts.inflate_bound _ _ A _ (hb i))

def bitBudget (F q M A : ℕ) : ℕ := 2*(M*(F*(q*BackendScalarBits.backendScalarUnit A.size)))+
  M*CompletedRootProducts.bitBudget F q A

def controlBudget (F q M : ℕ) : ℕ := 2*(M*(CompletedRootProducts.inflateControl F q+32)+8)+
  (M*(CompletedRootProducts.controlBudget F q+32)+8)+16

theorem execute_bits {F q M : ℕ} [NeZero q] (left right : Vector (RootRequestSelection.Selected (F*q)) M)
    (A : ℕ) (ha : BoundRows A left) (hb : BoundRows A right) :
    (execute left right).bitSteps≤bitBudget F q M A := by
  have hla := tabulate_bits left _ (fun i => CompletedRootProducts.inflate_bits F q A (left.get i).output (ha i))
  have hlb := tabulate_bits right _ (fun i => CompletedRootProducts.inflate_bits F q A (right.get i).output (hb i))
  have hp : (execute left right).value.products.bitSteps≤M*CompletedRootProducts.bitBudget F q A := by
    apply tabulate_bits
    intro i
    apply CompletedRootProducts.execute_bits _ _ A <;> rw [tabulate_get]
    · exact CompletedRootProducts.inflate_bound _ _ A _ (ha i)
    · exact CompletedRootProducts.inflate_bound _ _ A _ (hb i)
  dsimp only [execute] at hp
  change _+_+_≤_
  unfold bitBudget
  omega

theorem execute_control {F q M : ℕ} [NeZero q] (left right : Vector (RootRequestSelection.Selected (F*q)) M) :
    (execute left right).control≤controlBudget F q M := by
  have hla := tabulate_control left _ (fun i => CompletedRootProducts.inflate_control F q (left.get i).output)
  have hlb := tabulate_control right _ (fun i => CompletedRootProducts.inflate_control F q (right.get i).output)
  have hp : (execute left right).value.products.control≤M*(CompletedRootProducts.controlBudget F q+32)+8 :=
    tabulate_control _ _ (fun _ => CompletedRootProducts.execute_control _ _)
  dsimp only [execute] at hp
  change _+_+_+16≤_
  unfold controlBudget
  omega

/-- Original selected rows remain in the enclosing record. This counts both
new inflated copies and the complete product arrays, with all residues. -/
def cells {F q M : ℕ} (out : Prepared F q M) : ℕ :=
  (out.left.value.toList.map (fun b => (b.toList.map (fun row => row.toArray.size)).sum)).sum+
  (out.right.value.toList.map (fun b => (b.toList.map (fun row => row.toArray.size)).sum)).sum+
  (out.products.value.toList.map (fun b => (b.toList.map (fun row => row.toArray.size)).sum)).sum

theorem cells_eq {F q M : ℕ} (out : Prepared F q M) :
    cells out=M*((2*F+CompletedRootProducts.outputLength F)*q) := by
  simp only [cells,Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms execute_polynomial
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
#print axioms cells_eq
end ThinMatrix.PairedRootRows
