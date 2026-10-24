import GraphOwnBandCollection
import GraphAdaptiveSourceBank
import HalfSourceCapSetup

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-! Concrete diagonal adaptive source preparation and retained completion
banks. SourceFormation.Program keeps the existing mixed source ledger explicit;
completion has separate binary steps and bounded indexed control. Neither
ledger is silently reclassified as machine bit time. Each source is produced
once per own band and middle block; each completion bank once per own band,
pair of masks and fixed root type. All opposite-band requests share it. -/
namespace ThinMatrix.GraphOwnBandPreparation
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n)

abbrev Stores := Vector (GraphAdaptiveBatchSources.Stored f p) S

def sourceBlock (a : Fin S) (b : Fin (CompactBlocks.blockCount n h)) (cap : ℕ) :
    SourceFormation.Program (GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t) :=
  let graph := GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val cap
  ⟨graph.encoded.value,GraphAdaptiveSourceBank.preparationRecorded f p graph+8⟩

def sourcesWith (cap : ℕ) : SourceFormation.Program (Stores f p (S:=S)) :=
  SourceFormation.vectorBuild S fun a =>
    SourceFormation.vectorBuild (CompactBlocks.blockCount n h) fun b =>
      sourceBlock f p hm input a b cap

/-- The support cap is computed once before the source loop. -/
def sources : SourceFormation.Program (Stores f p (S:=S)) :=
  let cap := HalfSourceCapSetup.execute p.m (p.L-p.m)
  let rows := sourcesWith f p hm input cap.value
  ⟨rows.value,cap.bitSteps+rows.operations+8⟩

@[simp] theorem sources_get (a : Fin S) (b : Fin (CompactBlocks.blockCount n h)) :
    (((sources f p hm input).value.get a).get b)=
      (GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val
        (HalfSourceSuffixChoice.limit p.m (p.L-p.m))).encoded.value := by
  simp only [sources,sourcesWith,SourceFormation.vectorBuild_get,sourceBlock,HalfSourceCapSetup.execute_value]

theorem sources_correct (a : Fin S) :
    GraphAdaptiveBatchSources.Correct f p hm input a.val a.val ((sources f p hm input).value.get a) := by
  intro b
  exact sources_get f p hm input a b

theorem sources_work :
    (sources f p hm input (S:=S)).operations=
      (HalfSourceCapSetup.execute p.m (p.L-p.m)).bitSteps+
      (∑ a : Fin S, ∑ b : Fin (CompactBlocks.blockCount n h),
        GraphAdaptiveSourceBank.preparationRecorded f p
          (GraphAdaptivePrefix.fromInputs f p hm b input a.val a.val
            (HalfSourceSuffixChoice.limit p.m (p.L-p.m))))+
      16*S*CompactBlocks.blockCount n h+8*S+8 := by
  simp only [sources,sourcesWith,SourceFormation.vectorBuild,sourceBlock,Vector.get_ofFn,
    HalfSourceCapSetup.execute_value,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

variable (base : Index f p)
  (stored : Stores f p (S:=S))
  (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))

abbrev BankRows := Vector (Prepared f p base) (GraphOwnBandCollection.G f p (S:=S))

def bank (g : Fin (GraphOwnBandCollection.G f p (S:=S))) : Run (Prepared f p base) :=
  let a := (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1
  let out := GraphAdaptiveRootBatch.prepare f p hm input a.val a.val (stored.get a) (hc a)
    (GraphOwnBandCollection.index f p base g)
  ⟨⟨out.value.banks,out.value.layouts⟩,out.bitSteps,
    out.control+64*(GraphOwnBandCollection.G f p (S:=S)).size^2+32⟩

/-- All groups are concretely tabulated, retained and addressed by their
canonical quotient/remainder index. Source arrays are only read here. -/
def banks : Run (BankRows f p base (S:=S)) :=
  tabulate (Vector.replicate (GraphOwnBandCollection.G f p (S:=S)) ())
    (bank f p hm input base stored hc)

def get (rows : BankRows f p base (S:=S)) (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    Prepared f p (GraphOwnBandCollection.index f p base g) :=
  ⟨(rows.get g).banks,(rows.get g).layouts⟩

@[simp] theorem banks_get (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    get f p base (banks f p hm input base stored hc).value g=
      (GraphAdaptiveRootBatch.prepare f p hm input
        (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val
        (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val
        (stored.get (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1)
        (hc (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1)
        (GraphOwnBandCollection.index f p base g)).value := by
  simp only [get,banks,tabulate_get,bank]

theorem banks_bits : (banks f p hm input base stored hc).bitSteps=
    ∑ g,(bank f p hm input base stored hc g).bitSteps := by
  exact tabulate_bits_eq _ _

theorem banks_control : (banks f p hm input base stored hc).control=
    (∑ g,(bank f p hm input base stored hc g).control)+
      32*GraphOwnBandCollection.G f p (S:=S)+8 := by
  exact tabulate_control_eq _ _

#print axioms sources_get
#print axioms sources_correct
#print axioms sources_work
#print axioms banks_get
#print axioms banks_bits
#print axioms banks_control
end ThinMatrix.GraphOwnBandPreparation
