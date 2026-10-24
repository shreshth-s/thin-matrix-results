import GraphAdaptiveRootCorrect
import GraphAdaptiveSourceBank

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 1800000

/-! The complete retained completion bank for an oriented root depends only
on its own physical band. Encoders and completion matrices are prepared once
per band and reused in every opposite-band query batch. Equality here concerns
retained values; the preparation counters are paid only at that first setup. -/
namespace ThinMatrix.GraphAdaptiveBankSharing
open GraphAdaptiveRootBatch
open GraphPrefixCompletion
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (a b a' b' : ℕ)
  (xs ys : GraphAdaptiveBatchSources.Stored f p)
  (hx : GraphAdaptiveBatchSources.Correct f p hm input a b xs)
  (hy : GraphAdaptiveBatchSources.Correct f p hm input a' b' ys)
  (i : GraphRootCompletion.Index p.L p.m p.t)
  (hs : if i.right then b=b' else a=a')

attribute [local irreducible] GraphAdaptivePrefix.fromInputs
include hm input a b a' b' hx hy hs

theorem pick_eq (block : Fin (CompactBlocks.blockCount n h)) (s : Fin (W f p)) :
    GraphAdaptiveBatchSources.pick f p (xs.get block) (i.atSlot s)=
      GraphAdaptiveBatchSources.pick f p (ys.get block) (i.atSlot s) := by
  rw [GraphAdaptiveBatchSources.pick_correct f p hm input a b xs hx,
    GraphAdaptiveBatchSources.pick_correct f p hm input a' b' ys hy]
  rcases i with ⟨u,v,run,normal,opposite,channel,right⟩
  cases right
  · have ha : a=a' := hs
    subst a'
    have hh := GraphAdaptivePrefix.left_independent f p hm block input a b b'
      (HalfSourceSuffixChoice.limit p.m (p.L-p.m)) u v run
    exact congrArg (fun family => (((family.get normal).get opposite).get channel)) hh
  · have hb : b=b' := hs
    subst b'
    have hh := GraphAdaptivePrefix.right_independent f p hm block input a a' b
      (HalfSourceSuffixChoice.limit p.m (p.L-p.m)) u v run
    exact congrArg (fun family => (((family.get normal).get opposite).get channel)) hh

theorem source_eq (block : Fin (CompactBlocks.blockCount n h)) (s : Fin (W f p)) :
    GraphAdaptiveBatchSources.source f p hm input a b xs hx block (i.atSlot s)=
      GraphAdaptiveBatchSources.source f p hm input a' b' ys hy block (i.atSlot s) := by
  rw [GraphAdaptiveBatchSources.source_correct,GraphAdaptiveBatchSources.source_correct,
    pick_eq f p hm input a b a' b' xs ys hx hy i hs]

theorem sources_eq : sources f p hm input a b xs hx i=sources f p hm input a' b' ys hy i := by
  apply Vector.ext
  intro s hs'
  apply Vector.ext
  intro block hb
  change (((sources f p hm input a b xs hx i).get ⟨s,hs'⟩).get ⟨block,hb⟩)=
    (((sources f p hm input a' b' ys hy i).get ⟨s,hs'⟩).get ⟨block,hb⟩)
  simp only [sources,Vector.get_ofFn]
  exact (GraphAdaptiveBatchSources.collect_get f p hm input a b xs hx (i.atSlot ⟨s,hs'⟩) ⟨block,hb⟩).trans
    ((source_eq f p hm input a b a' b' xs ys hx hy i hs ⟨block,hb⟩ ⟨s,hs'⟩).trans
      (GraphAdaptiveBatchSources.collect_get f p hm input a' b' ys hy (i.atSlot ⟨s,hs'⟩) ⟨block,hb⟩).symm)

theorem prepare_value_eq : (prepare f p hm input a b xs hx i).value=
    (prepare f p hm input a' b' ys hy i).value := by
  have hb : (prepare f p hm input a b xs hx i).value.banks=
      (prepare f p hm input a' b' ys hy i).value.banks := by
    apply Vector.ext
    intro s hs'
    have hh := prepare_bank f p hm input a b xs hx i ⟨s,hs'⟩
    rw [sources_eq f p hm input a b a' b' xs ys hx hy i hs] at hh
    exact hh.trans (prepare_bank f p hm input a' b' ys hy i ⟨s,hs'⟩).symm
  have hl : (prepare f p hm input a b xs hx i).value.layouts=
      (prepare f p hm input a' b' ys hy i).value.layouts := by
    apply Vector.ext
    intro s hs'
    exact (prepare_layout f p hm input a b xs hx i ⟨s,hs'⟩).trans
      (prepare_layout f p hm input a' b' ys hy i ⟨s,hs'⟩).symm
  exact congrArg₂ (fun banks layouts => (⟨banks,layouts⟩ : GraphAdaptiveRootBatch.Prepared f p i)) hb hl

#print axioms pick_eq
#print axioms source_eq
#print axioms sources_eq
#print axioms prepare_value_eq
end ThinMatrix.GraphAdaptiveBankSharing
