import GraphRootProductCosts
import WeightedRootProducts

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

/-! From one retained graph to paired, shifted and weighted cyclic output
rows. Every request is executed, including unmatched requests. The source
identity is a weighted coefficient sum, not yet the full LOW-count identity. -/
namespace ThinMatrix.GraphWeightedRootProducts
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (b ell : ℕ) where
  paired : GraphRootProducts.Prepared f p b ell
  counts : Run (ℕ×ℕ)
  weighted : Run (WeightedRootProducts.Prepared (CompletedRootProducts.outputLength (p.m+1)) f.cyclic p.t (FoldedBackendExecution.windowQuerySize n))

def execute {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) : Run (Prepared f p b ell) :=
  let paired := GraphRootProducts.execute graph i target bandL bandR
  let counts := RetainedRootWindows.weights (graph.permuted.transformed.source.roots.keys.value.channels.get i.channel)
  let weighted := WeightedRootProducts.prepare (2*p.m) p.t (counts.value.1+counts.value.2) paired.paired.value.products.value
  ⟨⟨paired,counts,weighted⟩,paired.newBitSteps+counts.bitSteps+weighted.bitSteps,paired.newControl+counts.control+weighted.control+24⟩

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootProducts.Index p.L p.m p.t) :=
  execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target bandL bandR

def card {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) : ℕ :=
  let c := graph.permuted.transformed.source.roots.keys.value.channels.get i.channel
  WalshEmbedding.ones (ResidualFamilyKeys.normal c).get+WalshEmbedding.ones (ResidualFamilyKeys.opposite c).get

/-- Specification uses only retained source polynomials and actual requests. -/
noncomputable def sourceValue {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  if GraphRootProducts.accepted graph i.leftIndex target bandL bandR request then
    ∑ d : Fin p.t, if card graph i≤d.val then (TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ)*
      ((GraphRootProducts.rootPolynomial graph i.leftIndex target request*
        GraphRootProducts.rootPolynomial graph (GraphRootProducts.transpose graph i).value target request).coeff (d.val-card graph i)) residue else 0
  else 0

def output {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (out : Prepared f p b ell)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) : Vector Cell f.cyclic :=
  (out.weighted.value.outputs.value.get request).sum.value

theorem fromInputs_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootProducts.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    view ((output (fromInputs f p block input bandL bandR ell i).value request).get residue)=
      sourceValue (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target bandL bandR request residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  change view (((WeightedRootProducts.prepare _ _ _ _).value.outputs.value.get request).sum.value.get residue)=_
  rw [WeightedRootProducts.prepare_value]
  have hp := GraphRootProducts.fromInputs_product f p block input bandL bandR ell i request
  dsimp only at hp
  change ResidualPolynomialDegree.decode ((GraphRootProducts.execute _ _ _ _ _).paired.value.products.value.get request)=_ at hp
  rw [hp,RetainedRootWindows.weights_value]
  unfold sourceValue card
  split <;> simp_all only [Polynomial.coeff_zero,CyclicRing.zero_coeff,mul_zero,ite_self,Finset.sum_const_zero]

def productMagnitude (L m q : ℕ) : ℕ := CompletedRootProducts.magnitude (m+1) q (GraphRootProducts.magnitude L m)
def magnitude (L m q t : ℕ) : ℕ := t*(2^(2*m)*productMagnitude L m q)

noncomputable def bitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  GraphRootProducts.bitBudget graph i target+2*RetainedRootWindows.countBudget p.m+
    (p.t*WeightedRootProducts.weightBudget (2*p.m) p.t+
      FoldedBackendExecution.windowQuerySize n*WeightedRootProducts.bitBudget p.t f.cyclic (2^(2*p.m)) (productMagnitude p.L p.m f.cyclic))

def controlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) : ℕ :=
  GraphRootProducts.controlBudget graph i+(32*p.m+24)+
    (p.t*(WeightedRootProducts.weightBudget (2*p.m) p.t+48)+8+3*p.t+4+
      (FoldedBackendExecution.windowQuerySize n*(WeightedRootProducts.controlBudget p.t f.cyclic+32)+8)+8)+24

theorem fromInputs_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootProducts.Index p.L p.m p.t)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((output (fromInputs f p block input bandL bandR ell i).value request).get residue)).natAbs≤ magnitude p.L p.m f.cyclic p.t :=
  WeightedRootProducts.prepare_bound _ _ _ _ _ (GraphRootProducts.fromInputs_bound f p block input bandL bandR ell i) request residue

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) (i : GraphRootProducts.Index p.L p.m p.t) :
    (fromInputs f p block input bandL bandR ell i).bitSteps≤
      bitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) i input.target := by
  apply Nat.add_le_add
  · exact Nat.add_le_add (GraphRootProducts.fromInputs_bits f p block input bandL bandR ell i) (RetainedRootWindows.weights_bits _)
  · exact WeightedRootProducts.prepare_bits _ _ _ _ _ (GraphRootProducts.fromInputs_bound f p block input bandL bandR ell i)

theorem execute_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (i : GraphRootProducts.Index p.L p.m p.t) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (execute graph i target bandL bandR).control≤controlBudget graph i := by
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (GraphRootProducts.execute_control graph i target bandL bandR) (RetainedRootWindows.weights_control _).le)
    (WeightedRootProducts.prepare_control _ _ _ _)) 24

#print axioms fromInputs_value
#print axioms fromInputs_bound
#print axioms fromInputs_bits
#print axioms execute_control
end ThinMatrix.GraphWeightedRootProducts
