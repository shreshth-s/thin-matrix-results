import GraphPhysicalQueries

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

/-! Join the actually executed LOW and HIGH families before normalization.
The sources, masks, physical query and common degree runs are derived from
retained graph inputs. No numerical answer is supplied. -/
namespace ThinMatrix.GraphLowHighJoin
open BinaryCell CompleteThinProduct PhysicalShiftedForms GraphPhysicalQueries ExactHalfSourcePlan
open scoped BigOperators
variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

noncomputable def low (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (u v : Fin (J p.m)) (run : ℤ) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let q := LowRequestLocator.physical graph target request
  let d := CroppedHighQueries.geometry graph.permuted.transformed.source.roots.source.shape q
  lowQuery (t:=p.t) d.embedding q.outside.get (source graph u v false run) (source graph u v true run) (lift true) (lift false)

noncomputable def high (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (u v : Fin (J p.m)) (run : ℤ) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let q := LowRequestLocator.physical graph target request
  let d := CroppedHighQueries.geometry graph.permuted.transformed.source.roots.source.shape q
  storedHigh (t:=p.t) rfl d.embedding q.outside.get d.left_cap d.right_cap
    (globalLeaf (source graph u v false run) (source graph u v true run) (lift true) (lift false))

noncomputable def inner (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (u v : Fin (J p.m)) (run : ℤ) : CyclicRing.Cyclic f.cyclic :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let q := LowRequestLocator.physical graph target request
  let d := CroppedHighQueries.geometry graph.permuted.transformed.source.roots.source.shape q
  TensorContraction.bilinear
    (absorbedInput d.embedding q.outside.get (source graph u v false run) (lift true))
    (absorbedInput d.embedding q.outside.get (source graph u v true run) (lift false))
    (fun a b => ∏ i, fullKernel (fun j => lift true (d.embedding j)) (fun j => lift false (d.embedding j)) i a b)

theorem one_run (graph : GraphPrefixProgram.Prepared f p b ell)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (u v : Fin (J p.m)) (run : ℤ) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    low graph target request u v run+high graph target request u v run=inner graph target request u v run := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact (inner_query_eq_low_add_storedHigh rfl p.t_le _ _ _ _ _ _ _ _).symm

theorem low_fromInputs (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)=
      if q.bandL=bandL ∧ q.bandR=bandR then
        ∑ u, ∑ v, ∑ run∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ), low graph input.target request u v run residue
      else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  dsimp only
  rw [GraphPhysicalLow.fromInputs_value]
  unfold GraphPhysicalLow.value
  dsimp only
  split_ifs
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro run _
    unfold GraphPhysicalLow.runValue
    rw [pencil_query,matched_embedding]
    rfl
  · rfl

theorem high_fromInputs (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    view ((CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value request).get residue)=
      if q.bandL=bandL ∧ q.bandR=bandR then
        ∑ u, ∑ v, ∑ run∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ), high graph input.target request u v run residue
      else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  dsimp only
  rw [ShiftedPhysicalHigh.fromInputs_value]
  simp_rw [CroppedHighCyclic.query_coefficient,stored_source]
  simp only [CroppedHighQueries.accepts,decide_eq_true_eq]
  split_ifs
  · simpa only [high] using
      congrArg (fun z : Fin (J p.m) → Fin (J p.m) → ℤ => ∑ u, ∑ v, z u v)
        (funext fun u => funext fun v => RetainedDegreeRuns.sum_runs p.m (fun run =>
          high (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) input.target request u v run residue))
  · simp only [Finset.sum_const_zero]

theorem joined_fromInputs (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := GraphPrefixProgram.fromInputs f p block input bandL bandR ell
    let q := LowRequestLocator.physical graph input.target request
    view ((RootProductCollection.output (GraphLowMaskAssembly.execute graph input.target bandL bandR).value request).get residue)+
      view ((CountedCyclicCollection.output (GraphHighFamily.execute graph input.target bandL bandR).2.value request).get residue)=
      if q.bandL=bandL ∧ q.bandR=bandR then
        ∑ u, ∑ v, ∑ run∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ), inner graph input.target request u v run residue
      else 0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  dsimp only
  rw [low_fromInputs,high_fromInputs]
  split_ifs
  · simp only [←Finset.sum_add_distrib,←CyclicRing.add_coeff,one_run]
  · rfl

#print axioms one_run
#print axioms low_fromInputs
#print axioms high_fromInputs
#print axioms joined_fromInputs
end ThinMatrix.GraphLowHighJoin
