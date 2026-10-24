import SelectedRootProduct
import PrefixBlockBatch

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Contract paired retained root rows for the requested cyclic coefficient
at every middle block. Reads include every formal-degree/cyclic entry. The
output has one scalar per occurrence and block, not q unused coefficients.
Row reads/writes use the explicit bounded indexed-control counter shared by
the surrounding batching code. -/
namespace ThinMatrix.SelectedRootRows
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators
variable {F q t B M : ℕ} [NeZero q]

def readBlock (row : Vector Cell (B*(F*q))) (block : Fin B) : Run (Block F q) :=
  ⟨Vector.ofFn (fun d => Vector.ofFn (fun r => row.get (PrefixBlockBatch.column block (finProdFinEquiv (d,r))))),
    0,16*(F*q)+8*F+8⟩

omit [NeZero q] in
@[simp] theorem readBlock_get (row : Vector Cell (B*(F*q))) (block : Fin B) (d : Fin F) (r : Fin q) :
    view (((readBlock row block).value.get d).get r)=
      view (row.get (PrefixBlockBatch.column block (finProdFinEquiv (d,r)))) := by
  simp only [readBlock,Vector.get_ofFn]

omit [NeZero q] in
theorem readBlock_bound (row : Vector Cell (B*(F*q))) (block : Fin B) (A : ℕ)
    (ha : ∀ c,(view (row.get c)).natAbs≤A) : Bound A (readBlock row block).value := by
  intro d r
  change (view (((readBlock row block).value.get d).get r)).natAbs≤A
  rw [readBlock_get]
  exact ha _

def entry (ws : Vector Cell t) (a b : Vector Cell (B*(F*q))) (card : ℕ) (r : Fin q) (block : Fin B) : Run Cell :=
  let x := readBlock a block
  let y := readBlock b block
  let out := SelectedRootProduct.execute ws x.value y.value card r
  ⟨out.value,x.bitSteps+y.bitSteps+out.bitSteps,x.control+y.control+out.control+16⟩

theorem entry_value (ws : Vector Cell t) (a b : Vector Cell (B*(F*q))) (card : ℕ) (r : Fin q) (block : Fin B) :
    view (entry ws a b card r block).value=
      ∑ d : Fin t, if card≤d.val then view (ws.get d)*
        ((ResidualPolynomialDegree.decode (readBlock a block).value*
          ResidualPolynomialDegree.decode (readBlock b block).value).coeff (d.val-card)) r else 0 :=
  SelectedRootProduct.execute_value _ _ _ _ _

def execute (ws : Vector Cell t) (a b : Vector (Vector Cell (B*(F*q))) M)
    (card : ℕ) (residues : Vector (Fin q) M) : Run (Vector (Vector Cell B) M) :=
  tabulate a (fun j => tabulate (Vector.replicate B ()) (fun block => entry ws (a.get j) (b.get j) card (residues.get j) block))

@[simp] theorem execute_get (ws : Vector Cell t) (a b : Vector (Vector Cell (B*(F*q))) M)
    (card : ℕ) (residues : Vector (Fin q) M) (j : Fin M) (block : Fin B) :
    ((execute ws a b card residues).value.get j).get block=
      (entry ws (a.get j) (b.get j) card (residues.get j) block).value := by
  simp only [execute,tabulate_get]

def RowsBound (A : ℕ) (a : Vector (Vector Cell (B*(F*q))) M) : Prop :=
  ∀ j c,(view ((a.get j).get c)).natAbs≤A

theorem execute_bound (ws : Vector Cell t) (a b : Vector (Vector Cell (B*(F*q))) M)
    (card W A : ℕ) (residues : Vector (Fin q) M)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : RowsBound A a) (hb : RowsBound A b)
    (j : Fin M) (block : Fin B) :
    (view (((execute ws a b card residues).value.get j).get block)).natAbs≤
      t*(W*SelectedRootProduct.productMagnitude q t A) := by
  rw [execute_get]
  exact SelectedRootProduct.execute_bound _ _ _ _ W A hw
    (readBlock_bound _ _ A (ha j)) (readBlock_bound _ _ A (hb j)) _

theorem execute_bits (ws : Vector Cell t) (a b : Vector (Vector Cell (B*(F*q))) M)
    (card W A : ℕ) (residues : Vector (Fin q) M)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W) (ha : RowsBound A a) (hb : RowsBound A b) :
    (execute ws a b card residues).bitSteps≤M*(B*SelectedRootProduct.bitBudget q t W A) := by
  apply tabulate_bits
  intro j
  apply tabulate_bits
  intro block
  have hh := SelectedRootProduct.execute_bits ws (readBlock (a.get j) block).value (readBlock (b.get j) block).value card W A hw
    (readBlock_bound _ _ A (ha j)) (readBlock_bound _ _ A (hb j)) (residues.get j)
  simpa only [entry,readBlock,Nat.zero_add] using hh

def controlBudget (F q t B M : ℕ) : ℕ :=
  M*(B*(2*(16*(F*q)+8*F+8)+SelectedRootProduct.controlBudget q t+48)+40)+8

theorem execute_control (ws : Vector Cell t) (a b : Vector (Vector Cell (B*(F*q))) M)
    (card : ℕ) (residues : Vector (Fin q) M) :
    (execute ws a b card residues).control≤controlBudget F q t B M := by
  apply tabulate_control
  intro j
  have hh := tabulate_control (Vector.replicate B ())
    (fun block => entry ws (a.get j) (b.get j) card (residues.get j) block)
    (W:=2*(16*(F*q)+8*F+8)+SelectedRootProduct.controlBudget q t+16) (by
      intro block
      have hc := SelectedRootProduct.execute_control ws (readBlock (a.get j) block).value
        (readBlock (b.get j) block).value card (residues.get j)
      dsimp only [entry,readBlock] at hc ⊢
      omega)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using hh

#print axioms readBlock_get
#print axioms readBlock_bound
#print axioms entry_value
#print axioms execute_get
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.SelectedRootRows
