import GraphLowRecombination
import ShiftedLowRunFilter

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! The actual recombined LOW output pairs source words only at equal signed
degrees in [-m,m]. Semantic run elimination does not remove charged executions. -/
namespace ThinMatrix.GraphLowDegreeFilter
open WalshEmbedding GoodMapEmbedding ExactHalfSourcePlan DistinguishedResidualSupport TensorContraction
open scoped BigOperators

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def degree {L : ℕ} (right : Bool) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : ℤ :=
  if right then (ones (normalP2Bits normal):ℤ)-(ones (oppositeWBits opposite):ℤ)
  else (ones (oppositeWBits opposite):ℤ)-(ones (normalP2Bits normal):ℤ)

theorem raw_filter (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (normal : Fin p.L → NormalLetter) (opposite : Fin p.L → OppositeLetter) :
    GraphLowRunSources.raw graph u v right run normal opposite=
      if degree right normal opposite=run then
        GraphLowRunSources.raw graph u v right (degree right normal opposite) normal opposite else 0 := by
  cases right <;> simp only [GraphLowRunSources.raw,degree,Bool.false_eq_true,↓reduceIte,rawLeftSource,rawRightSource]
  all_goals split_ifs <;> first | rfl | simp_all

noncomputable def freeFactor (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    RetainedShiftedFactor.Data p.m (p.L-p.m) → Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  GraphLowRunSources.source (fun normal opposite => GraphLowRunSources.raw graph u v right (degree right normal opposite) normal opposite)
    (graph.permuted.transformed.source.roots.keys.value.masks.get a)
    (graph.permuted.transformed.source.roots.keys.value.masks.get b) (GraphShiftedRootFactors.forms graph right a b target request)

def wordDegree (graph : GraphPrefixProgram.Prepared f p b ell) (right : Bool)
    (a b : Fin (goodSlots p.L p.m).card) (x : RetainedShiftedFactor.Data p.m (p.L-p.m)) : ℤ :=
  degree right
    (RetainedShiftedFactor.normalInput (graph.permuted.transformed.source.roots.keys.value.masks.get a)
      (graph.permuted.transformed.source.roots.keys.value.masks.get b) x.1 x.2.1)
    (RetainedShiftedFactor.oppositeInput (graph.permuted.transformed.source.roots.keys.value.masks.get a)
      (graph.permuted.transformed.source.roots.keys.value.masks.get b) x.1 x.2.2)

theorem factor_filter (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (x : RetainedShiftedFactor.Data p.m (p.L-p.m)) :
    GraphLowRunSources.factor graph u v right run a b target request x=
      if wordDegree graph right a b x=run then freeFactor graph u v right a b target request x else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphLowRunSources.factor freeFactor GraphLowRunSources.source wordDegree cropBoth CroppedSourceContraction.crop
  rw [raw_filter]
  split_ifs <;> simp_all

noncomputable def kernel (x y : RetainedShiftedFactor.Data p.m (p.L-p.m)) : Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  (∏ i, ShiftedLowChannelFormula.localPencil (x.2.1 i) (y.2.2 i))*
    ∏ i, ShiftedLowChannelFormula.localPencil (y.2.1 i) (x.2.2 i)

noncomputable def paired (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  ∑ x, ∑ y, if wordDegree graph false a b x=wordDegree graph true b a y ∧
      wordDegree graph false a b x∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ) then
    weightedLow (2*p.m) p.t (freeFactor graph u v false a b target request x*
      freeFactor graph u v true b a target request y*kernel (f:=f) x y) residue else 0

theorem sum_runs (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (J p.m))
    (a b : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (∑ d∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ), GraphLowRecombination.runValue graph u v d a b target request residue)=
      paired graph u v a b target request residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  have h := ShiftedLowRunFilter.run_filter p.m (2*p.m) p.t
    (freeFactor graph u v false a b target request) (freeFactor graph u v true b a target request)
    (wordDegree graph false a b) (wordDegree graph true b a) (kernel (f:=f))
  have he := congrArg (fun z : CyclicRing.Cyclic f.cyclic => z residue) h
  simp only [CyclicRing.sum_coeff] at he
  unfold GraphLowRecombination.runValue ShiftedLowChannelFormula.pencil paired
  have hl (d : ℤ) : GraphLowRunSources.factor graph u v false d a b target request=
      fun x => if wordDegree graph false a b x=d then freeFactor graph u v false a b target request x else 0 :=
    funext (factor_filter graph u v false d a b target request)
  have hr (d : ℤ) : GraphLowRunSources.factor graph u v true d b a target request=
      fun y => if wordDegree graph true b a y=d then freeFactor graph u v true b a target request y else 0 :=
    funext (factor_filter graph u v true d b a target request)
  simp_rw [hl,hr]
  apply he.trans
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  split <;> rfl

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  let q := LowRequestLocator.physical graph target request
  if q.bandL=bandL ∧ q.bandR=bandR then
    ∑ u, ∑ v, paired graph u v (RootRequestSelection.rowRank q.row) (RootRequestSelection.rowRank q.column) target request residue
  else 0

theorem fromInputs_value (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    BinaryCell.view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)=
      value graph input.target bandL bandR request residue := by
  dsimp only
  rw [GraphLowRecombination.fromInputs_value]
  unfold GraphLowRecombination.value value
  simp_rw [sum_runs]

#print axioms raw_filter
#print axioms factor_filter
#print axioms sum_runs
#print axioms fromInputs_value
end ThinMatrix.GraphLowDegreeFilter
