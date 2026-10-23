import PhysicalOrdinaryForms

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! The executed all-mask LOW functional on full physical source words.
The same original masked sources, runs, request labels and cyclic ring are
used; no returned query value or preprocessed source is assumed. -/
namespace ThinMatrix.GraphPhysicalLow
open WalshEmbedding GoodMapEmbedding ResidualFamilyKeys DistinguishedResidualSupport RetainedShiftedFactor PhysicalWordReindex
open scoped BigOperators

private theorem sum_words {L m : ℕ} {R : Type*} [AddCommMonoid R]
    (a b : Mask L m) (F : Words L → R) (hz : ∀ w, ¬Supported a w → F w=0) :
    (∑ x : Data m (L-m), F (pack a b x))=∑ w, F w := by
  simpa only [Fintype.sum_prod_type] using sum_physical a b F hz

theorem sum_pairs {L m : ℕ} {R : Type*} [AddCommMonoid R]
    (a b : Mask L m) (F : Words L → Words L → R)
    (hl : ∀ x y, ¬Supported a x → F x y=0) (hr : ∀ x y, ¬Supported b y → F x y=0) :
    (∑ x : Data m (L-m), ∑ y : Data m (L-m), F (pack a b x) (pack b a y))=∑ x, ∑ y, F x y := by
  have hi (x : Data m (L-m)) := sum_words b a (F (pack a b x)) (hr (pack a b x))
  simp_rw [hi]
  apply sum_words a b (fun x => ∑ y, F x y)
  intro x hx
  simp only [hl x _ hx,Finset.sum_const_zero]

noncomputable def kernel {L m : ℕ} {R : Type*} [CommRing R]
    (a b : Mask L m) (x y : Words L) : Polynomial R :=
  (∏ i, ShiftedLowChannelFormula.localPencil (x.1 (selectedPosition a i)) (y.2 (selectedPosition a i)))*
    ∏ i, ShiftedLowChannelFormula.localPencil (y.1 (selectedPosition b i)) (x.2 (selectedPosition b i))

theorem kernel_pack {L m : ℕ} {R : Type*} [CommRing R]
    (a b : Mask L m) (x y : Data m (L-m)) :
    kernel (R:=R) a b (pack a b x) (pack b a y)=
      (∏ i, ShiftedLowChannelFormula.localPencil (x.2.1 i) (y.2.2 i))*
        ∏ i, ShiftedLowChannelFormula.localPencil (y.2.1 i) (x.2.2 i) := by
  simp only [kernel,pack_normal_selected,pack_opposite_selected]

variable {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
  {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f}

def mask (graph : GraphPrefixProgram.Prepared f p b ell) (i : Fin (goodSlots p.L p.m).card) : Mask p.L p.m :=
  graph.permuted.transformed.source.roots.keys.value.masks.get i

noncomputable def absorbed (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (w : Words p.L) : Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  ((PhysicalOrdinaryForms.ordinary (mask graph a) (mask graph b) right (LowRequestLocator.physical graph target request).outside w : ℤ) : Polynomial (CyclicRing.Cyclic f.cyclic))*
    Polynomial.C (CroppedSourceContraction.crop (p.m/2) (GraphLowRunSources.raw graph u v right run) w.1 w.2)

theorem absorbed_zero (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (w : Words p.L) (hw : ¬Supported (mask graph a) w) :
    absorbed graph u v right run a b target request w=0 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  simp [absorbed,PhysicalOrdinaryForms.ordinary_zero _ _ _ _ w hw]

theorem factor_pack (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (right : Bool) (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (x : Data p.m (p.L-p.m)) :
    GraphLowRunSources.factor graph u v right run a b target request x=
      absorbed graph u v right run a b target request (pack (mask graph a) (mask graph b) x) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  rw [GraphLowRunSources.factor_value,PhysicalOrdinaryForms.graph_product]
  rfl

noncomputable def pencil (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    Polynomial (CyclicRing.Cyclic f.cyclic) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  ∑ x, ∑ y, absorbed graph u v false run a b target request x*
    absorbed graph u v true run b a target request y*kernel (mask graph a) (mask graph b) x y

theorem pencil_reindex (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n)) :
    letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
    ShiftedLowChannelFormula.pencil (GraphLowRunSources.factor graph u v false run a b target request)
      (GraphLowRunSources.factor graph u v true run b a target request)
      (fun x => x.2.1) (fun x => x.2.2) (fun x => x.2.1) (fun x => x.2.2)=pencil graph u v run a b target request := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold ShiftedLowChannelFormula.pencil TensorContraction.bilinear pencil
  simp_rw [factor_pack,← kernel_pack (R:=CyclicRing.Cyclic f.cyclic) (mask graph a) (mask graph b)]
  apply sum_pairs (mask graph a) (mask graph b) (fun x y =>
    absorbed graph u v false run a b target request x*absorbed graph u v true run b a target request y*
      kernel (mask graph a) (mask graph b) x y)
  · intro x y hx
    rw [absorbed_zero graph u v false run a b target request x hx,zero_mul,zero_mul]
  · intro x y hy
    rw [absorbed_zero graph u v true run b a target request y hy,mul_zero,zero_mul]

noncomputable def runValue (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (residue : Fin f.cyclic) : ℤ :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  TensorContraction.weightedLow (2*p.m) p.t (pencil graph u v run a b target request) residue

theorem run_reindex (graph : GraphPrefixProgram.Prepared f p b ell) (u v : Fin (ExactHalfSourcePlan.J p.m))
    (run : ℤ) (a b : Fin (goodSlots p.L p.m).card)
    (target : BinaryFoldedFormation.BinaryTable n) (request : Fin (FoldedBackendExecution.windowQuerySize n))
    (residue : Fin f.cyclic) :
    GraphLowRecombination.runValue graph u v run a b target request residue=runValue graph u v run a b target request residue := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold GraphLowRecombination.runValue runValue
  rw [pencil_reindex]

noncomputable def value (graph : GraphPrefixProgram.Prepared f p b ell) (target : BinaryFoldedFormation.BinaryTable n)
    (bandL bandR : ℕ) (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) : ℤ :=
  let q := LowRequestLocator.physical graph target request
  if q.bandL=bandL ∧ q.bandR=bandR then
    ∑ u, ∑ v, ∑ d∈Finset.Icc (-(p.m:ℤ)) (p.m:ℤ),
      runValue graph u v d (RootRequestSelection.rowRank q.row) (RootRequestSelection.rowRank q.column) target request residue
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
  simp_rw [run_reindex]

#print axioms sum_pairs
#print axioms kernel_pack
#print axioms absorbed_zero
#print axioms factor_pack
#print axioms pencil_reindex
#print axioms run_reindex
#print axioms fromInputs_value
end ThinMatrix.GraphPhysicalLow
