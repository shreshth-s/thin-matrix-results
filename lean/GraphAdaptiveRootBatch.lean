import GraphAdaptiveLegacy
import FullyRetainedRootBatch

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 2200000

/-! Shared completion consumes the actual adaptive sources from every middle
block. Each window matrix bank and layout is prepared once for reuse across
opposite bands. Execution uses the addressed rectangular backend and sums all
windows and all degree/cyclic columns. The legacy routine appears only in the
correctness specification; it is not executed by this program. -/
namespace ThinMatrix.GraphAdaptiveRootBatch
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open RectangularBatch (Scheme)
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev Index := GraphRootCompletion.Index p.L p.m p.t
abbrev E (i : Index f p) := GraphAdaptiveCompatibility.typeLength p.L p.m p.t i.channel
abbrev W := RetainedRootWindows.slots (p.L-p.m)
abbrev D (i : Index f p) := WindowSharedCompletion.D (p.L-p.m) (E f p i) (p.m/2)
  (GraphWindowCompatibility.counts i.channel).1 (GraphWindowCompatibility.counts i.channel).2
abbrev Bank (i : Index f p) := FullyRetainedRootBatch.Bank (p.L-p.m) (E f p i) (p.m/2)
  (GraphWindowCompatibility.counts i.channel).1 (GraphWindowCompatibility.counts i.channel).2
  ((p.m+1)*f.cyclic) (CompactBlocks.blockCount n h)
abbrev Sources (i : Index f p) := FullyRetainedRootBatch.Sources (p.L-p.m) (E f p i) (p.m/2)
  (GraphWindowCompatibility.counts i.channel).1 (GraphWindowCompatibility.counts i.channel).2
  ((p.m+1)*f.cyclic) (CompactBlocks.blockCount n h)

structure Prepared (i : Index f p) where
  banks : Vector (Bank f p i) (W f p)
  layouts : Vector (RetainedWindowPermutation.Layout (2*(p.L-p.m))) (W f p)

variable (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
  (stored : GraphAdaptiveBatchSources.Stored f p)
  (hc : GraphAdaptiveBatchSources.Correct f p hm input bandL bandR stored)
  (i : Index f p)

def prepare : Run (Prepared f p i) :=
  let shape := Vector.replicate (W f p) ()
  let banks := tabulate shape (fun s => GraphAdaptiveBatchSources.prepare f p hm input bandL bandR stored hc (i.atSlot s))
  let maps := tabulate shape (fun s => RetainedWindowPermutation.build (p.L-p.m) (min (E f p i) (p.L-p.m))
    (decide ((GraphWindowCompatibility.counts i.channel).2≤(GraphWindowCompatibility.counts i.channel).1)) s)
  ⟨⟨banks.value,maps.value⟩,banks.bitSteps+maps.bitSteps,banks.control+maps.control+3*W f p+16⟩

/-- Specification of the retained compatible source arrays. -/
def sources : Vector (Sources f p i) (W f p) := Vector.ofFn (fun s =>
  (GraphAdaptiveBatchSources.collect f p hm input bandL bandR stored hc (i.atSlot s)).value)

@[simp] theorem prepare_bank (s : Fin (W f p)) :
    (prepare f p hm input bandL bandR stored hc i).value.banks.get s=
      (SharedPrefixSourceBank.prepare ((sources f p hm input bandL bandR stored hc i).get s)).value := by
  simp only [prepare,tabulate_get,GraphAdaptiveBatchSources.prepare_value,sources,Vector.get_ofFn]
  rfl

@[simp] theorem prepare_layout (s : Fin (W f p)) :
    (prepare f p hm input bandL bandR stored hc i).value.layouts.get s=
      GraphWindowCompatibility.layout p.L p.m (E f p i) p.t (i.atSlot s) := by
  simp only [prepare,tabulate_get]
  rfl

theorem sources_layout (s : Fin (W f p)) (b : Fin (CompactBlocks.blockCount n h)) :
    (((sources f p hm input bandL bandR stored hc i).get s).get b).grouped.keys=
      GroupedPreparation.keyVector (WindowPrefixProgram.length (p.L-p.m) (E f p i))
        (WindowPrefixProgram.cap (p.L-p.m) (E f p i) (p.m/2)
          (GraphWindowCompatibility.counts i.channel).1 (GraphWindowCompatibility.counts i.channel).2) ∧
    (((sources f p hm input bandL bandR stored hc i).get s).get b).grouped.pairs=
      GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) (E f p i)) := by
  simpa only [sources,Vector.get_ofFn,GraphAdaptiveBatchSources.S,GraphAdaptiveBatchSources.R,
    GraphAdaptiveBatchSources.E,GraphRootCompletion.Index.atSlot,E] using
    GraphAdaptiveBatchSources.collect_layout f p hm input bandL bandR stored hc (i.atSlot s) b

theorem prepare_bits :
    (prepare f p hm input bandL bandR stored hc i).bitSteps=
      ∑ s : Fin (W f p),(GraphAdaptiveBatchSources.prepare f p hm input bandL bandR stored hc (i.atSlot s)).bitSteps := by
  simp only [prepare,tabulate_bits_eq,RetainedWindowPermutation.build,Finset.sum_const_zero,Nat.add_zero]

theorem prepare_control :
    (prepare f p hm input bandL bandR stored hc i).control=
      (∑ s : Fin (W f p),(GraphAdaptiveBatchSources.prepare f p hm input bandL bandR stored hc (i.atSlot s)).control)+
        W f p*(256*(p.L-p.m)+99)+32 := by
  simp only [prepare,tabulate_control_eq,RetainedWindowPermutation.build,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

omit hm input bandL bandR stored hc in
def execute {A Z : ℕ} (scheme : Scheme) (hD : 0<D f p i) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D f p i)^scheme.num) (hlast : Z≤(D f p i)^scheme.z)
    (bank : Prepared f p i) (labels : Array (Vector (Fin 4) (2*(p.L-p.m)))) :
    Run (RootProductCollection.Prepared (Vector (Vector Cell ((CompactBlocks.blockCount n h)*((p.m+1)*f.cyclic))) labels.size)
      (W f p) labels.size ((CompactBlocks.blockCount n h)*((p.m+1)*f.cyclic))) :=
  FullyRetainedRootBatch.execute scheme hD hA hZ hfirst hlast bank.banks bank.layouts labels

omit hm stored hc in
def reference (b : Fin (CompactBlocks.blockCount n h)) (s : Fin (W f p))
    (labels : Array (Vector (Fin 4) (2*(p.L-p.m)))) (j : Fin labels.size) : Vector Cell ((p.m+1)*f.cyclic) :=
  let graph := GraphPrefixProgram.fromInputs f p b input bandL bandR (E f p i)
  let out := WindowCompletionProgram.execute (GraphPrefixCompletion.encodedSlot graph (i.atSlot s))
    (GraphPrefixCompletion.permuted graph (i.atSlot s)).layout labels
  (out.completed.value.requests[j.val]'(by simp [out])).output

attribute [local irreducible] GraphAdaptiveBatchSources.collect GraphAdaptiveBatchSources.source GraphPrefixProgram.fromInputs

theorem correct {A Z : ℕ} (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<D f p i) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(D f p i)^scheme.num) (hlast : Z≤(D f p i)^scheme.z)
    (labels : Array (Vector (Fin 4) (2*(p.L-p.m)))) (j : Fin labels.size)
    (b : Fin (CompactBlocks.blockCount n h)) (c : Fin ((p.m+1)*f.cyclic)) :
    view ((RootProductCollection.output (execute f p i scheme hD hA hZ hfirst hlast
      (prepare f p hm input bandL bandR stored hc i).value labels).value j).get (PrefixBlockBatch.column b c))=
      ∑ s : Fin (W f p),view ((reference f p input bandL bandR i b s labels j).get c) := by
  have hh := FullyRetainedRootBatch.correct
    (k:=p.L-p.m) (ell:=E f p i) (total:=p.m/2)
    (cn:=(GraphWindowCompatibility.counts i.channel).1) (co:=(GraphWindowCompatibility.counts i.channel).2)
    (C:=(p.m+1)*f.cyclic) (B:=CompactBlocks.blockCount n h) (W:=W f p) scheme hv hD hA hZ hfirst hlast
    (sources f p hm input bandL bandR stored hc i)
    (prepare f p hm input bandL bandR stored hc i).value.banks
    (prepare_bank f p hm input bandL bandR stored hc i)
    (fun s b => (sources_layout f p hm input bandL bandR stored hc i s b).1)
    (fun s b => (sources_layout f p hm input bandL bandR stored hc i s b).2)
    (prepare f p hm input bandL bandR stored hc i).value.layouts labels j b c
  dsimp only [execute]
  rw [hh]
  apply Finset.sum_congr rfl
  intro s _
  simp only [sources,Vector.get_ofFn,prepare_layout]
  have he := GraphAdaptiveBatchSources.collect_get f p hm input bandL bandR stored hc (i.atSlot s) b
  have hr := congrArg (fun x : GraphAdaptiveBatchSources.Source f p (i.atSlot s) =>
    view ((PrefixCompletionProgram.row x (PrefixCompletionMatrices.prepare x).value
      ((WindowCompletionRequests.requests (E f p i)
        (GraphWindowCompatibility.layout p.L p.m (E f p i) p.t (i.atSlot s)) labels).value[j.val]'(by simp))).value.output.get c)) he
  exact hr.trans (GraphAdaptiveLegacy.row_eq f p hm b input bandL bandR (i.atSlot s) stored hc labels j c)

#print axioms prepare_bank
#print axioms prepare_layout
#print axioms sources_layout
#print axioms prepare_bits
#print axioms prepare_control
#print axioms correct
end ThinMatrix.GraphAdaptiveRootBatch
