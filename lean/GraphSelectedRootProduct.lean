import SelectedRootRows
import GraphWeightedRootProducts
import GraphSharedTargets

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

/-! A single requested cyclic coefficient of the actual completed graph-root
product. Full degree/cyclic source rows are consumed, but only one cyclic dot
product is evaluated per formal-degree pair. This refines the old complete
polynomial specification without running its unused output coefficients. -/
namespace ThinMatrix.GraphSelectedRootProduct
open BinaryCell BinaryResidualPolynomial
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

attribute [local irreducible] GraphPrefixProgram.fromInputs

theorem decode_root (input : BinaryFoldedFormation.Inputs n) (a b ell : ℕ)
    (i : GraphRootCompletion.Index p.L p.m p.t)
    (block : Fin (CompactBlocks.blockCount n h))
    (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (row : Vector Cell ((CompactBlocks.blockCount n h)*((p.m+1)*f.cyclic)))
    (hr : ∀ c,view (row.get (PrefixBlockBatch.column block c))=
      view (((GraphRootCompletion.fromInputs f p block input a b ell i).completed.value.sums.value.get request).output.get c)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    ResidualPolynomialDegree.decode (SelectedRootRows.readBlock row block).value=
      GraphRootProducts.rootPolynomial (GraphPrefixProgram.fromInputs f p block input a b ell) i input.target request := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  apply Polynomial.ext
  intro d
  funext residue
  rw [ResidualPolynomialDegree.decode_coeff]
  by_cases hd : d<p.m+1
  · simp only [hd,↓reduceDIte]
    change view ((((SelectedRootRows.readBlock row block).value).get ⟨d,hd⟩).get residue)=_
    rw [SelectedRootRows.readBlock_get,hr]
    rw [GraphRootCompletion.fromInputs_contraction f p block input a b ell i request ⟨d,hd⟩ residue]
    simp only [GraphRootProducts.rootPolynomial,CompletedRootProducts.polynomialOf_coeff,hd,↓reduceDIte]
    rfl
  · simp only [hd,↓reduceDIte,GraphRootProducts.rootPolynomial,CompletedRootProducts.polynomialOf_coeff]

theorem entry_value (input : BinaryFoldedFormation.Inputs n) (a b ell : ℕ)
    (i : GraphRootProducts.Index p.L p.m p.t)
    (block : Fin (CompactBlocks.blockCount n h))
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic)
    (ws : Vector Cell p.t)
    (hw : ∀ d,view (ws.get d)=(TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ))
    (left right : Vector Cell ((CompactBlocks.blockCount n h)*((p.m+1)*f.cyclic)))
    (hl : ∀ c,view (left.get (PrefixBlockBatch.column block c))=
      view (((GraphRootCompletion.fromInputs f p block input a b ell i.leftIndex).completed.value.sums.value.get request).output.get c))
    (hr : ∀ c,view (right.get (PrefixBlockBatch.column block c))=
      view (((GraphRootCompletion.fromInputs f p block input a b ell
        (GraphRootProducts.transpose (GraphPrefixProgram.fromInputs f p block input a b ell) i).value).completed.value.sums.value.get request).output.get c))
    (ha : GraphRootProducts.accepted (GraphPrefixProgram.fromInputs f p block input a b ell) i.leftIndex input.target a b request=true) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    view (SelectedRootRows.entry ws left right
      (GraphWeightedRootProducts.card (GraphPrefixProgram.fromInputs f p block input a b ell) i) residue block).value=
      GraphWeightedRootProducts.sourceValue (GraphPrefixProgram.fromInputs f p block input a b ell) i input.target a b request residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [SelectedRootRows.entry_value,decode_root f p input a b ell i.leftIndex block request left hl,
    decode_root f p input a b ell _ block request right hr]
  simp only [GraphWeightedRootProducts.sourceValue,ha,ite_true,hw]

#print axioms decode_root
#print axioms entry_value
end ThinMatrix.GraphSelectedRootProduct
