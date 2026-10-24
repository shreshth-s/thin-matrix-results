import GraphOwnBandPreparation
import GraphHighPreparation

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 1800000

/-! Produce each diagonal cropped source exactly once and retain both its raw
source families (for HIGH) and adaptive encodings (for LOW). Views only copy
references; neither view reruns source construction or either encoder. -/
namespace ThinMatrix.GraphSharedSourceProduction
open BinaryCell BinaryGroupedCoordinates SourceFormation
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)

abbrev Entry := ExactHalfBandSources.Families p.L p.m f.cyclic ×
  GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t
abbrev Stores := Vector (Vector (Entry f p) (CompactBlocks.blockCount n h)) S

def sourceBlock (a : Fin S) (b : Fin (CompactBlocks.blockCount n h)) (cap : ℕ) : Program (Entry f p) :=
  let graph := GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val cap
  ⟨(graph.roots.source.sources.value,graph.encoded.value),GraphAdaptiveSourceBank.preparationRecorded f p graph+16⟩

def sourcesWith (cap : ℕ) : Program (Stores f p (S:=S)) :=
  vectorBuild S fun a => vectorBuild (CompactBlocks.blockCount n h) fun b => sourceBlock f p hm input a b cap

def execute : Program (Stores f p (S:=S)) :=
  let cap := HalfSourceCapSetup.execute p.m (p.L-p.m)
  let rows := sourcesWith f p hm input cap.value
  ⟨rows.value,cap.bitSteps+rows.operations+8⟩

omit hm input in
def low (stored : Stores f p (S:=S)) : Program (GraphOwnBandPreparation.Stores f p (S:=S)) :=
  vectorBuild S fun a => vectorBuild (CompactBlocks.blockCount n h) fun b => ⟨((stored.get a).get b).2,16⟩

omit hm input in
def high (stored : Stores f p (S:=S)) (block : Fin (CompactBlocks.blockCount n h)) :
    Program (GraphRetainedHigh.Sources f p (K:=S)) :=
  vectorBuild S fun a => ⟨((stored.get a).get block).1,16⟩

theorem low_correct (a : Fin S) : GraphAdaptiveBatchSources.Correct f p hm input a.val a.val
    ((low f p (execute f p hm input).value).value.get a) := by
  intro b
  simp only [low,execute,sourcesWith,sourceBlock,vectorBuild_get,HalfSourceCapSetup.execute_value]

theorem high_correct (block : Fin (CompactBlocks.blockCount n h)) :
    GraphRetainedHigh.Correct f p block input (Vector.ofFn (fun a : Fin S=>a.val))
      (high f p (execute f p hm input).value block).value := by
  intro a
  simp only [high,execute,sourcesWith,sourceBlock,vectorBuild_get,HalfSourceCapSetup.execute_value,Vector.get_ofFn]
  rfl

theorem work : (execute f p hm input (S:=S)).operations=
    (HalfSourceCapSetup.execute p.m (p.L-p.m)).bitSteps+
      (∑ a : Fin S,∑ b : Fin (CompactBlocks.blockCount n h),
        GraphAdaptiveSourceBank.preparationRecorded f p
          (GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val (HalfSourceSuffixChoice.limit p.m (p.L-p.m))))+
      24*S*CompactBlocks.blockCount n h+8*S+8 := by
  simp only [execute,sourcesWith,sourceBlock,vectorBuild,Vector.get_ofFn,HalfSourceCapSetup.execute_value,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

omit hm input in
 theorem low_work (stored : Stores f p (S:=S)) : (low f p stored).operations=24*S*CompactBlocks.blockCount n h+8*S := by
  simp only [low,vectorBuild,Vector.get_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

omit hm input in
 theorem high_work (stored : Stores f p (S:=S)) (block : Fin (CompactBlocks.blockCount n h)) :
    (high f p stored block).operations=24*S := by
  simp only [high,vectorBuild,Vector.get_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

#print axioms low_correct
#print axioms high_correct
#print axioms work
#print axioms low_work
#print axioms high_work
end ThinMatrix.GraphSharedSourceProduction
