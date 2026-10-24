import GraphAdaptivePrefixCosts

/-! A retained source bank evaluates a diagonal preparation only once for
 each band. Pair assembly reads the left preparation of one band and the
 right preparation of the other; it never runs the encoders again. The
 accounting here preserves the existing mixed preparation ledger and does
 not turn that partial ledger into a full bit-runtime theorem. -/
namespace ThinMatrix.GraphAdaptiveSourceBank
open ExactHalfSourcePlan
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (hm : p.m ≤ p.L-p.m)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

def preparationRecorded {b : ℕ} (graph : GraphAdaptivePrefix.Prepared f p b) : ℕ :=
  let roots := graph.roots
  let src := roots.source
  src.shape.operations+src.selectors.bitSteps+src.selectors.control+src.folded.bitSteps+
    src.leftBand.operations+src.rightBand.operations+src.sources.operations+
    roots.keys.bitSteps+roots.keys.control+roots.roots.bitSteps+roots.roots.control+
    graph.encoded.bitSteps+graph.encoded.control

abbrev Bank (K : ℕ) := Vector (GraphAdaptivePrefix.Prepared f p block) K

def prepare {K : ℕ} (ids : Vector ℕ K) (cap : ℕ) : SourceFormation.Program (Bank f p block K) :=
  SourceFormation.vectorBuild K fun i =>
    let graph := GraphAdaptivePrefix.fromInputs f p hm block input (ids.get i) (ids.get i) cap
    ⟨graph,preparationRecorded f p graph⟩

theorem prepare_get {K : ℕ} (ids : Vector ℕ K) (cap : ℕ) (i : Fin K) :
    (prepare f p hm block input ids cap).value.get i=
      GraphAdaptivePrefix.fromInputs f p hm block input (ids.get i) (ids.get i) cap :=
  SourceFormation.vectorBuild_get _ _ _

theorem prepare_recorded_work {K : ℕ} (ids : Vector ℕ K) (cap : ℕ) :
    (prepare f p hm block input ids cap).operations=
      (∑ i, preparationRecorded f p
        (GraphAdaptivePrefix.fromInputs f p hm block input (ids.get i) (ids.get i) cap))+8*K := by
  simp only [prepare,SourceFormation.vectorBuild,Vector.get_ofFn]

theorem prepare_recorded_bound {K : ℕ} (ids : Vector ℕ K) (cap budget : ℕ)
    (hb : ∀ i, preparationRecorded f p
      (GraphAdaptivePrefix.fromInputs f p hm block input (ids.get i) (ids.get i) cap)≤budget) :
    (prepare f p hm block input ids cap).operations≤(budget+8)*K :=
  SourceFormation.vectorBuild_cost _ _ _ hb

/-- All nested vectors contain references to the already retained encoded
families. The only new structure has polynomial size in the tensor dimension. -/
def assemble {K : ℕ} (bank : Bank f p block K) (a b : Fin K) :
    GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t :=
  Vector.ofFn fun u => Vector.ofFn fun v => Vector.ofFn fun run =>
    (((((bank.get a).encoded.value.get u).get v).get run).1,
     ((((bank.get b).encoded.value.get u).get v).get run).2)

theorem assemble_get {K : ℕ} (bank : Bank f p block K) (a b : Fin K)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (((assemble f p block bank a b).get u).get v).get run=
      (((((bank.get a).encoded.value.get u).get v).get run).1,
       ((((bank.get b).encoded.value.get u).get v).get run).2) := by
  simp only [assemble,Vector.get_ofFn]

attribute [local irreducible] GraphAdaptivePrefix.fromInputs

/-- The entire encoded result agrees, not only its numerical tensor view. -/
theorem assemble_prepared {K : ℕ} (ids : Vector ℕ K) (cap : ℕ) (a b : Fin K) :
    assemble f p block (prepare f p hm block input ids cap).value a b=
      (GraphAdaptivePrefix.fromInputs f p hm block input (ids.get a) (ids.get b) cap).encoded.value := by
  apply Vector.ext; intro u hu
  apply Vector.ext; intro v hv
  apply Vector.ext; intro run hrun
  change (((assemble f p block (prepare f p hm block input ids cap).value a b).get ⟨u,hu⟩).get ⟨v,hv⟩).get ⟨run,hrun⟩=_
  rw [assemble_get,prepare_get,prepare_get]
  apply Prod.ext
  · exact GraphAdaptivePrefix.left_independent f p hm block input (ids.get a) (ids.get a) (ids.get b) cap ⟨u,hu⟩ ⟨v,hv⟩ ⟨run,hrun⟩
  · exact GraphAdaptivePrefix.right_independent f p hm block input (ids.get b) (ids.get a) (ids.get b) cap ⟨u,hu⟩ ⟨v,hv⟩ ⟨run,hrun⟩

/-- Explicit branch/copy sites for assembling the small family spine. The
arrays themselves are shared; machine-address prices are a further refinement. -/
def assembleProgram {K : ℕ} (bank : Bank f p block K) (a b : Fin K) :
    SourceFormation.Program (GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t) :=
  SourceFormation.vectorBuild (J p.m) fun u => SourceFormation.vectorBuild (J p.m) fun v =>
    SourceFormation.vectorBuild (2*p.m+1) fun run =>
      ⟨((((((bank.get a).encoded.value.get u).get v).get run).1,
         ((((bank.get b).encoded.value.get u).get v).get run).2)),12⟩

theorem assembleProgram_value {K : ℕ} (bank : Bank f p block K) (a b : Fin K) :
    (assembleProgram f p block bank a b).value=assemble f p block bank a b := by
  apply Vector.ext; intro u hu
  apply Vector.ext; intro v hv
  apply Vector.ext; intro run hrun
  change ((((assembleProgram f p block bank a b).value.get ⟨u,hu⟩).get ⟨v,hv⟩).get ⟨run,hrun⟩)=
    (((assemble f p block bank a b).get ⟨u,hu⟩).get ⟨v,hv⟩).get ⟨run,hrun⟩
  simp only [assembleProgram,SourceFormation.vectorBuild_get,assemble,Vector.get_ofFn]

theorem assembleProgram_sites {K : ℕ} (bank : Bank f p block K) (a b : Fin K) :
    (assembleProgram f p block bank a b).operations=
      ((20*(2*p.m+1)+8)*J p.m+8)*J p.m := by
  simp only [assembleProgram,SourceFormation.vectorBuild,Vector.get_ofFn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

#print axioms assembleProgram_value
#print axioms assembleProgram_sites

#print axioms prepare_get
#print axioms prepare_recorded_work
#print axioms prepare_recorded_bound
#print axioms assemble_get
#print axioms assemble_prepared
end ThinMatrix.GraphAdaptiveSourceBank
