import GraphAdaptiveCompatibility
import GraphAdaptivePrefixCosts
import SharedPrefixSourceBank

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000

/-! Extract compatible prefix sources from retained adaptive graph records.
Only proof casts and a small vector spine are formed here: no window partition,
transform or encoder is rerun. The vector length is the actual middle-block
count, and the complete formal-degree/cyclic column dimension is retained. -/
namespace ThinMatrix.GraphAdaptiveBatchSources
open BinaryGroupedCoordinates BinaryGroupedPreparation
open GraphPrefixCompletion GraphAdaptiveCompatibility

variable {k C ell ell' total cn co : ℕ}

def transport (h : ell=ell') (x : WindowPrefixProgram.Prepared k ell C) : WindowPrefixProgram.Prepared k ell' C :=
  cast (congrArg (fun e => WindowPrefixProgram.Prepared k e C) h) x

theorem transport_execute (h : ell=ell') (X : OppositeWindowLayer.Source (2*k) C) :
    transport h (WindowPrefixProgram.execute ell total cn co X).value=
      (WindowPrefixProgram.execute ell' total cn co X).value := by cases h; rfl

def extract (x : WindowPrefixProgram.Prepared k ell C)
    (h : x.rareCap=WindowPrefixProgram.cap k ell total cn co) :
    CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell) (WindowPrefixProgram.length k ell)
      (WindowPrefixProgram.cap k ell total cn co) C :=
  cast (congrArg (fun r => CappedPrefixProgram.Prepared (WindowPrefixProgram.prefixLength k ell)
    (WindowPrefixProgram.length k ell) r C) h) x.encoded

theorem extract_execute (x : WindowPrefixProgram.Prepared k ell C)
    (X : OppositeWindowLayer.Source (2*k) C) (hx : x=(WindowPrefixProgram.execute ell total cn co X).value)
    (h : x.rareCap=WindowPrefixProgram.cap k ell total cn co) :
    extract x h=(WindowPrefixProgram.execute ell total cn co X).value.encoded := by cases hx; rfl

variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev Stored := Vector (GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t) (CompactBlocks.blockCount n h)

def pick (results : GraphAdaptivePrefix.Results p.L p.m f.cyclic p.t) (index : Index p.L p.m p.t) :
    GraphAdaptivePrefix.Entry p.L p.m f.cyclic :=
  (((side index.right (((results.get index.u).get index.v).get index.run)).get index.normal).get index.opposite).get index.channel

def Correct (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ) (stored : Stored f p) : Prop :=
  ∀ b,stored.get b=(GraphAdaptivePrefix.fromInputs f p hm b input bandL bandR (HalfSourceSuffixChoice.limit p.m (p.L-p.m))).encoded.value

theorem pick_correct (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
    (stored : Stored f p) (hc : Correct f p hm input bandL bandR stored) (b : Fin (CompactBlocks.blockCount n h))
    (index : Index p.L p.m p.t) : pick f p (stored.get b) index=
      selected (GraphAdaptivePrefix.fromInputs f p hm b input bandL bandR (HalfSourceSuffixChoice.limit p.m (p.L-p.m))) index := by
  rw [hc b]
  rfl

abbrev E (index : Index p.L p.m p.t) := typeLength p.L p.m p.t index.channel
abbrev P (index : Index p.L p.m p.t) := WindowPrefixProgram.prefixLength (p.L-p.m) (E f p index)
abbrev S (index : Index p.L p.m p.t) := WindowPrefixProgram.length (p.L-p.m) (E f p index)
abbrev R (index : Index p.L p.m p.t) := WindowPrefixProgram.cap (p.L-p.m) (E f p index) (p.m/2)
  (GraphWindowCompatibility.counts index.channel).1 (GraphWindowCompatibility.counts index.channel).2
abbrev Source (index : Index p.L p.m p.t) := CappedPrefixProgram.Prepared (P f p index) (S f p index) (R f p index) ((p.m+1)*f.cyclic)

variable (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n) (bandL bandR : ℕ)
  (stored : Stored f p) (hc : Correct f p hm input bandL bandR stored)

include hm input bandL bandR hc

theorem pick_length (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    GraphAdaptivePrefix.length (pick f p (stored.get b) index)=E f p index := by
  rw [pick_correct f p hm input bandL bandR stored hc]
  exact selected_length hm b input bandL bandR index

def window (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    WindowPrefixProgram.Prepared (p.L-p.m) (E f p index) ((p.m+1)*f.cyclic) :=
  transport (pick_length f p hm input bandL bandR stored hc b index)
    ((pick f p (stored.get b) index).prepared.encoded.get index.slot)

theorem window_correct (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    window f p hm input bandL bandR stored hc b index=
      (WindowPrefixProgram.execute (E f p index) (p.m/2) (GraphWindowCompatibility.counts index.channel).1
        (GraphWindowCompatibility.counts index.channel).2
        ((pick f p (stored.get b) index).prepared.permuted.get index.slot).coefficients).value := by
  have hprefix := selected_prefix hm b input bandL bandR (HalfSourceSuffixChoice.limit p.m (p.L-p.m)) index
  have hprefix' : (pick f p (stored.get b) index).prepared.encoded.get index.slot=
      (WindowPrefixProgram.execute (GraphAdaptivePrefix.length (pick f p (stored.get b) index)) (p.m/2)
        (GraphWindowCompatibility.counts index.channel).1 (GraphWindowCompatibility.counts index.channel).2
        ((pick f p (stored.get b) index).prepared.permuted.get index.slot).coefficients).value := by
    rw [pick_correct f p hm input bandL bandR stored hc]
    exact hprefix
  exact (congrArg (transport (pick_length f p hm input bandL bandR stored hc b index)) hprefix').trans
    (transport_execute _ _)

def source (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) : Source f p index :=
  extract (window f p hm input bandL bandR stored hc b index)
    (congrArg WindowPrefixProgram.Prepared.rareCap (window_correct f p hm input bandL bandR stored hc b index))

theorem source_correct (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    source f p hm input bandL bandR stored hc b index=
      (WindowPrefixProgram.execute (E f p index) (p.m/2) (GraphWindowCompatibility.counts index.channel).1
        (GraphWindowCompatibility.counts index.channel).2
        ((pick f p (stored.get b) index).prepared.permuted.get index.slot).coefficients).value.encoded :=
  extract_execute _ _ (window_correct f p hm input bandL bandR stored hc b index) _

def collect (index : Index p.L p.m p.t) : Run (Vector (Source f p index) (CompactBlocks.blockCount n h)) :=
  tabulate stored (fun b => ⟨source f p hm input bandL bandR stored hc b index,0,16⟩)

@[simp] theorem collect_get (index : Index p.L p.m p.t) (b : Fin (CompactBlocks.blockCount n h)) :
    (collect f p hm input bandL bandR stored hc index).value.get b=source f p hm input bandL bandR stored hc b index := by
  simp only [collect,tabulate_get]

theorem collect_bits (index : Index p.L p.m p.t) : (collect f p hm input bandL bandR stored hc index).bitSteps=0 := by
  simp only [collect,tabulate_bits_eq,Finset.sum_const_zero]

theorem collect_control (index : Index p.L p.m p.t) :
    (collect f p hm input bandL bandR stored hc index).control ≤ 48*CompactBlocks.blockCount n h+8 := by
  have hh := tabulate_control stored (fun b => (⟨source f p hm input bandL bandR stored hc b index,0,16⟩ : Run (Source f p index)))
    (W:=16) (by intro b; rfl)
  simpa only [collect,Nat.mul_comm] using hh

theorem source_layout (index : Index p.L p.m p.t) (b : Fin (CompactBlocks.blockCount n h)) :
    (source f p hm input bandL bandR stored hc b index).grouped.keys=GroupedPreparation.keyVector (S f p index) (R f p index) ∧
    (source f p hm input bandL bandR stored hc b index).grouped.pairs=GroupedPreparation.pairKeys (S f p index) := by
  rw [source_correct]
  simp only [WindowPrefixProgram.execute,CappedPrefixProgram.execute,RetainedCappedGroups.prepare,
    GroupedPreparation.storeKeys_value,GroupedPreparation.storePairs_value,and_self]

def prepare (index : Index p.L p.m p.t) :
    Run (SharedPrefixSourceBank.Prepared (P f p index) (S f p index) (R f p index) ((p.m+1)*f.cyclic) (CompactBlocks.blockCount n h)) :=
  let xs := collect f p hm input bandL bandR stored hc index
  let banks := SharedPrefixSourceBank.prepare xs.value
  ⟨banks.value,xs.bitSteps+banks.bitSteps,xs.control+banks.control+8⟩

theorem prepare_value (index : Index p.L p.m p.t) :
    (prepare f p hm input bandL bandR stored hc index).value=
      (SharedPrefixSourceBank.prepare (collect f p hm input bandL bandR stored hc index).value).value := rfl

def rawMagnitude : ℕ := 2^p.m*(4^p.m*2^(p.L+p.m))
def windowMagnitude : ℕ := 2^(p.L-p.m)*rawMagnitude f p

omit hc in
theorem selected_root_bound (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    ResidualWindowSource.BoundRows
      (GraphAdaptiveCompatibility.root (GraphAdaptivePrefix.fromInputs f p hm b input bandL bandR
        (HalfSourceSuffixChoice.limit p.m (p.L-p.m))) index) (rawMagnitude f p) := by
  have hh := GraphRootWindows.root_bound f p b input bandL bandR index.u index.v index.run
  rcases index with ⟨u,v,run,i,j,c,slot,right⟩
  cases right
  · exact hh.1 i j c
  · exact hh.2 i j c

theorem source_magnitude (b : Fin (CompactBlocks.blockCount n h)) (index : Index p.L p.m p.t) :
    OppositeWindowLayer.Bound ((pick f p (stored.get b) index).prepared.permuted.get index.slot).coefficients
      (windowMagnitude f p) := by
  rw [pick_correct f p hm input bandL bandR stored hc,selected_entry]
  exact GraphAdaptivePrefixCosts.permuted_bound _ _ (rawMagnitude f p)
    (selected_root_bound f p hm input bandL bandR b index) index.slot

theorem source_leaf_bound (index : Index p.L p.m p.t) (b : Fin (CompactBlocks.blockCount n h))
    (pair : Fin (2^(S f p index))) :
    PrefixCompletionMatrices.LeafBound ((source f p hm input bandL bandR stored hc b index).traces.get pair)
      (2^(P f p index)*windowMagnitude f p) := by
  intro j q c
  rw [source_correct]
  exact CappedPrefixProgram.output_bound _ _ (windowMagnitude f p)
    (WindowPrefixProgram.castSource_bound _ _ _ (source_magnitude f p hm input bandL bandR stored hc b index)) pair j q c

theorem collect_layout (index : Index p.L p.m p.t) (b : Fin (CompactBlocks.blockCount n h)) :
    ((collect f p hm input bandL bandR stored hc index).value.get b).grouped.keys=GroupedPreparation.keyVector (S f p index) (R f p index) ∧
    ((collect f p hm input bandL bandR stored hc index).value.get b).grouped.pairs=GroupedPreparation.pairKeys (S f p index) := by
  rw [collect_get]
  exact source_layout f p hm input bandL bandR stored hc index b

theorem prepare_bits (index : Index p.L p.m p.t) :
    (prepare f p hm input bandL bandR stored hc index).bitSteps ≤
      CompactBlocks.blockCount n h*(2^(S f p index)*
        PrefixCompletionMatrices.bitBudget (P f p index) (CappedSubsetList.count (S f p index) (R f p index))
          ((p.m+1)*f.cyclic) (2^(P f p index)*windowMagnitude f p)) := by
  have hh := SharedPrefixSourceBank.prepare_bits (collect f p hm input bandL bandR stored hc index).value
    (2^(P f p index)*windowMagnitude f p) (by
      intro b pair
      rw [collect_get]
      exact source_leaf_bound f p hm input bandL bandR stored hc index b pair)
  simp only [prepare,collect_bits,zero_add]
  exact hh

theorem prepare_control (index : Index p.L p.m p.t) :
    (prepare f p hm input bandL bandR stored hc index).control ≤
      48*CompactBlocks.blockCount n h+8+
      (CompactBlocks.blockCount n h*(2^(S f p index)*
        (PrefixCompletionMatrices.controlBudget (P f p index) (CappedSubsetList.count (S f p index) (R f p index))
          ((p.m+1)*f.cyclic)+32)+40)+GroupedPreparation.keyBudget (S f p index) (R f p index)+
        GroupedPreparation.keyBudget (S f p index) (S f p index)+28)+8 := by
  exact Nat.add_le_add_right (Nat.add_le_add (collect_control f p hm input bandL bandR stored hc index)
    (SharedPrefixSourceBank.prepare_control _)) 8

#print axioms selected_root_bound
#print axioms source_magnitude
#print axioms source_leaf_bound
#print axioms collect_layout
#print axioms prepare_bits
#print axioms prepare_control
#print axioms transport_execute
#print axioms extract_execute
#print axioms pick_correct
#print axioms pick_length
#print axioms window_correct
#print axioms source_correct
#print axioms collect_get
#print axioms collect_bits
#print axioms collect_control
#print axioms source_layout
#print axioms prepare_value
end ThinMatrix.GraphAdaptiveBatchSources
