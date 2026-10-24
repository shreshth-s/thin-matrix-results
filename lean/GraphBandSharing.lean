import GraphPrefixProgram

/-! Per-side source preparation is independent of the opposite band. This
allows one retained diagonal preparation per band, rather than rebuilding
source encoders once for every band pair. It does not assert a full runtime. -/
namespace ThinMatrix.GraphBandSharing
open ExactHalfSourcePlan
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

theorem sources_left_independent (a b₁ b₂ : ℕ) (u v : Fin (J p.m)) :
    (((ExactHalfGraphSources.execute f p block input a b₁).sources.value.get u).get v).1=(((ExactHalfGraphSources.execute f p block input a b₂).sources.value.get u).get v).1 := by
  simp only [ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms sources_left_independent

theorem sources_right_independent (a₁ a₂ b : ℕ) (u v : Fin (J p.m)) :
    (((ExactHalfGraphSources.execute f p block input a₁ b).sources.value.get u).get v).2=(((ExactHalfGraphSources.execute f p block input a₂ b).sources.value.get u).get v).2 := by
  simp only [ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms sources_right_independent

theorem roots_left_independent (a b₁ b₂ : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphResidualFamilies.fromInputs f p block input a b₁).roots.value.get u).get v).get run).1=((((GraphResidualFamilies.fromInputs f p block input a b₂).roots.value.get u).get v).get run).1 := by
  simp only [GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms roots_left_independent

theorem roots_right_independent (a₁ a₂ b : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphResidualFamilies.fromInputs f p block input a₁ b).roots.value.get u).get v).get run).2=((((GraphResidualFamilies.fromInputs f p block input a₂ b).roots.value.get u).get v).get run).2 := by
  simp only [GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms roots_right_independent

theorem windows_left_independent (a b₁ b₂ : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphRootWindows.fromInputs f p block input a b₁ ell).windows.value.get u).get v).get run).1=((((GraphRootWindows.fromInputs f p block input a b₂ ell).windows.value.get u).get v).get run).1 := by
  simp only [GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms windows_left_independent

theorem windows_right_independent (a₁ a₂ b : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphRootWindows.fromInputs f p block input a₁ b ell).windows.value.get u).get v).get run).2=((((GraphRootWindows.fromInputs f p block input a₂ b ell).windows.value.get u).get v).get run).2 := by
  simp only [GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms windows_right_independent

theorem transformed_left_independent (a b₁ b₂ : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphWindowTransforms.fromInputs f p block input a b₁ ell).transformed.value.get u).get v).get run).1=((((GraphWindowTransforms.fromInputs f p block input a b₂ ell).transformed.value.get u).get v).get run).1 := by
  simp only [GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms transformed_left_independent

theorem transformed_right_independent (a₁ a₂ b : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphWindowTransforms.fromInputs f p block input a₁ b ell).transformed.value.get u).get v).get run).2=((((GraphWindowTransforms.fromInputs f p block input a₂ b ell).transformed.value.get u).get v).get run).2 := by
  simp only [GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms transformed_right_independent

theorem permuted_left_independent (a b₁ b₂ : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphWindowPermutations.fromInputs f p block input a b₁ ell).permuted.value.get u).get v).get run).1=((((GraphWindowPermutations.fromInputs f p block input a b₂ ell).permuted.value.get u).get v).get run).1 := by
  simp only [GraphWindowPermutations.execute_get,
    GraphWindowPermutations.fromInputs,
    GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms permuted_left_independent

theorem permuted_right_independent (a₁ a₂ b : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphWindowPermutations.fromInputs f p block input a₁ b ell).permuted.value.get u).get v).get run).2=((((GraphWindowPermutations.fromInputs f p block input a₂ b ell).permuted.value.get u).get v).get run).2 := by
  simp only [GraphWindowPermutations.execute_get,
    GraphWindowPermutations.fromInputs,
    GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms permuted_right_independent

theorem encoded_left_independent (a b₁ b₂ : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphPrefixProgram.fromInputs f p block input a b₁ ell).encoded.value.get u).get v).get run).1=((((GraphPrefixProgram.fromInputs f p block input a b₂ ell).encoded.value.get u).get v).get run).1 := by
  simp only [GraphPrefixProgram.execute_get,
    GraphPrefixProgram.fromInputs,
    GraphWindowPermutations.execute_get,
    GraphWindowPermutations.fromInputs,
    GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms encoded_left_independent

theorem encoded_right_independent (a₁ a₂ b : ℕ) (ell : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    ((((GraphPrefixProgram.fromInputs f p block input a₁ b ell).encoded.value.get u).get v).get run).2=((((GraphPrefixProgram.fromInputs f p block input a₂ b ell).encoded.value.get u).get v).get run).2 := by
  simp only [GraphPrefixProgram.execute_get,
    GraphPrefixProgram.fromInputs,
    GraphWindowPermutations.execute_get,
    GraphWindowPermutations.fromInputs,
    GraphWindowTransforms.execute_get,
    GraphWindowTransforms.fromInputs,
    GraphRootWindows.execute_get,
    GraphRootWindows.fromInputs,
    GraphResidualFamilies.execute_get,
    GraphResidualFamilies.fromInputs,
    ExactHalfBandSources.allPairs_get,
    ExactHalfGraphSources.execute]

#print axioms encoded_right_independent

end ThinMatrix.GraphBandSharing
