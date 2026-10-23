import GraphWeightedRootProducts
import RootProductCollection

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-! Execute the retained strict channel list, every run and every pair of
translation-list indices for one good-mask pair and one block/band pair.
The graph preparation is shared; per-root targets and all unmatched requests
remain executed and charged. The result is an explicit weighted source sum,
not yet the shifted five-term LOW count or the complete modular backend. -/
namespace ThinMatrix.GraphRootFamilyProducts
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GoodMapEmbedding ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

def channels {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  RootProductCollection.execute (graph.permuted.transformed.source.roots.keys.value.channels) (fun c => GraphWeightedRootProducts.execute graph ⟨u,v,run,left,right,c⟩ target bandL bandR) GraphWeightedRootProducts.output

noncomputable def channelsBitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun (c : Fin (channelCount p.m p.t)) => GraphWeightedRootProducts.bitBudget graph ⟨u,v,run,left,right,c⟩ target) (FoldedBackendExecution.windowQuerySize n) f.cyclic (GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)

def channelsControlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card) : ℕ :=
  RootProductCollection.controlBudget (fun (c : Fin (channelCount p.m p.t)) => GraphWeightedRootProducts.controlBudget graph ⟨u,v,run,left,right,c⟩) (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem channels_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (channels (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v run left right input.target bandL bandR).value request).get residue)).natAbs≤(channelCount p.m p.t)*(GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t) := by
  apply RootProductCollection.execute_bound _ _ _ (GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t) _ request residue
  intro c
  exact GraphWeightedRootProducts.fromInputs_bound f p block input bandL bandR ell ⟨u,v,run,left,right,c⟩

theorem channels_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card) :
    (channels (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v run left right input.target bandL bandR).bitSteps≤
      channelsBitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v run left right input.target := by
  apply RootProductCollection.execute_bits _ _ _ (GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)
  · intro c
    exact GraphWeightedRootProducts.fromInputs_bound f p block input bandL bandR ell ⟨u,v,run,left,right,c⟩
  · intro c
    exact GraphWeightedRootProducts.fromInputs_bits f p block input bandL bandR ell ⟨u,v,run,left,right,c⟩

theorem channels_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (channels graph u v run left right target bandL bandR).control≤channelsControlBudget graph u v run left right := by
  apply RootProductCollection.execute_control
  intro c
  exact GraphWeightedRootProducts.execute_control graph ⟨u,v,run,left,right,c⟩ target bandL bandR

def runs {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  RootProductCollection.execute ((graph.encoded.value.get u).get v) (fun run => channels graph u v run left right target bandL bandR) RootProductCollection.output

noncomputable def runsBitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun (run : Fin (2*p.m+1)) => channelsBitBudget graph u v run left right target) (FoldedBackendExecution.windowQuerySize n) f.cyclic (channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)

def runsControlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) : ℕ :=
  RootProductCollection.controlBudget (fun (run : Fin (2*p.m+1)) => channelsControlBudget graph u v run left right) (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem runs_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (runs (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v left right input.target bandL bandR).value request).get residue)).natAbs≤(2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t) := by
  apply RootProductCollection.execute_bound _ _ _ (channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t) _ request residue
  intro run
  exact channels_bound f p block input bandL bandR ell u v run left right

theorem runs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) :
    (runs (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v left right input.target bandL bandR).bitSteps≤
      runsBitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u v left right input.target := by
  apply RootProductCollection.execute_bits _ _ _ (channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)
  · intro run
    exact channels_bound f p block input bandL bandR ell u v run left right
  · intro run
    exact channels_bits f p block input bandL bandR ell u v run left right

theorem runs_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u v : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (runs graph u v left right target bandL bandR).control≤runsControlBudget graph u v left right := by
  apply RootProductCollection.execute_control
  intro run
  exact channels_control graph u v run left right target bandL bandR

def rightTranslations {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  RootProductCollection.execute (graph.encoded.value.get u) (fun v => runs graph u v left right target bandL bandR) RootProductCollection.output

noncomputable def rightTranslationsBitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun (v : Fin (J p.m)) => runsBitBudget graph u v left right target) (FoldedBackendExecution.windowQuerySize n) f.cyclic ((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t))

def rightTranslationsControlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) : ℕ :=
  RootProductCollection.controlBudget (fun (v : Fin (J p.m)) => runsControlBudget graph u v left right) (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem rightTranslations_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (rightTranslations (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u left right input.target bandL bandR).value request).get residue)).natAbs≤(J p.m)*((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)) := by
  apply RootProductCollection.execute_bound _ _ _ ((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)) _ request residue
  intro v
  exact runs_bound f p block input bandL bandR ell u v left right

theorem rightTranslations_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) :
    (rightTranslations (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u left right input.target bandL bandR).bitSteps≤
      rightTranslationsBitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell) u left right input.target := by
  apply RootProductCollection.execute_bits _ _ _ ((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t))
  · intro v
    exact runs_bound f p block input bandL bandR ell u v left right
  · intro v
    exact runs_bits f p block input bandL bandR ell u v left right

theorem rightTranslations_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
    (u : Fin (J p.m)) (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (rightTranslations graph u left right target bandL bandR).control≤rightTranslationsControlBudget graph u left right := by
  apply RootProductCollection.execute_control
  intro v
  exact runs_control graph u v left right target bandL bandR

def execute {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
     (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :=
  RootProductCollection.execute (graph.encoded.value) (fun u => rightTranslations graph u left right target bandL bandR) RootProductCollection.output

noncomputable def executeBitBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
     (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) : ℕ :=
  RootProductCollection.bitBudget (fun (u : Fin (J p.m)) => rightTranslationsBitBudget graph u left right target) (FoldedBackendExecution.windowQuerySize n) f.cyclic (J p.m*((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)))

def executeControlBudget {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
     (left right : Fin (goodSlots p.L p.m).card) : ℕ :=
  RootProductCollection.controlBudget (fun (u : Fin (J p.m)) => rightTranslationsControlBudget graph u left right) (FoldedBackendExecution.windowQuerySize n) f.cyclic

theorem execute_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
     (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    (view ((RootProductCollection.output (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell)  left right input.target bandL bandR).value request).get residue)).natAbs≤(J p.m)*(J p.m*((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t))) := by
  apply RootProductCollection.execute_bound _ _ _ (J p.m*((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t))) _ request residue
  intro u
  exact rightTranslations_bound f p block input bandL bandR ell u left right

theorem execute_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
     (left right : Fin (goodSlots p.L p.m).card) :
    (execute (GraphPrefixProgram.fromInputs f p block input bandL bandR ell)  left right input.target bandL bandR).bitSteps≤
      executeBitBudget (GraphPrefixProgram.fromInputs f p block input bandL bandR ell)  left right input.target := by
  apply RootProductCollection.execute_bits _ _ _ (J p.m*((2*p.m+1)*(channelCount p.m p.t*GraphWeightedRootProducts.magnitude p.L p.m f.cyclic p.t)))
  · intro u
    exact rightTranslations_bound f p block input bandL bandR ell u left right
  · intro u
    exact rightTranslations_bits f p block input bandL bandR ell u left right

theorem execute_control {n h r b ell : ℕ} {f : CompactBlocks.PhysicalFactorization r}
    {p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f} (graph : GraphPrefixProgram.Prepared f p b ell)
     (left right : Fin (goodSlots p.L p.m).card) (target : BinaryFoldedFormation.BinaryTable n) (bandL bandR : ℕ) :
    (execute graph  left right target bandL bandR).control≤executeControlBudget graph  left right := by
  apply RootProductCollection.execute_control
  intro u
  exact rightTranslations_control graph u left right target bandL bandR

theorem fromInputs_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (left right : Fin (goodSlots p.L p.m).card)
    (request : Fin (FoldedBackendExecution.windowQuerySize n)) (residue : Fin f.cyclic) :
    let graph := (GraphPrefixProgram.fromInputs f p block input bandL bandR ell)
    view ((RootProductCollection.output (execute graph left right input.target bandL bandR).value request).get residue)=
      ∑ u : Fin (J p.m), ∑ v : Fin (J p.m), ∑ run : Fin (2*p.m+1), ∑ c : Fin (channelCount p.m p.t),
        GraphWeightedRootProducts.sourceValue graph ⟨u,v,run,left,right,c⟩ input.target bandL bandR request residue := by
  dsimp only
  simp only [execute,rightTranslations,runs,channels,RootProductCollection.execute_value]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro run _
  apply Finset.sum_congr rfl; intro c _
  exact GraphWeightedRootProducts.fromInputs_value f p block input bandL bandR ell ⟨u,v,run,left,right,c⟩ request residue

#print axioms channels_bound
#print axioms channels_bits
#print axioms channels_control
#print axioms runs_bound
#print axioms runs_bits
#print axioms runs_control
#print axioms rightTranslations_bound
#print axioms rightTranslations_bits
#print axioms rightTranslations_control
#print axioms execute_bound
#print axioms execute_bits
#print axioms execute_control
#print axioms fromInputs_value
end ThinMatrix.GraphRootFamilyProducts
