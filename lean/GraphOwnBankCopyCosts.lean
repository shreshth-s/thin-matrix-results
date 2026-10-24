import GraphOwnBandPreparation
import HalfSourceBatchCopyVolume

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBankCopyCosts
open BinaryGroupedCoordinates BinaryGroupedPreparation GraphAdaptiveRootBatch
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (base : Index f p)

def P := WindowPrefixProgram.prefixLength (p.L-p.m) (E f p base)
def len := WindowPrefixProgram.length (p.L-p.m) (E f p base)
def cap := WindowPrefixProgram.cap (p.L-p.m) (E f p base) (p.m/2)
  (GraphWindowCompatibility.counts base.channel).1 (GraphWindowCompatibility.counts base.channel).2
def H := 2^(P f p base)*GraphAdaptiveBatchSources.windowMagnitude f p
def V := CompactBlocks.blockCount n h*((p.m+1)*f.cyclic)*
  HalfSourcePrefixVolume.groups (P f p base) (len f p base) (cap f p base)
def bits := W f p*V f p base*BackendScalarBits.backendScalarUnit (H f p base).size
def control := W f p*(V f p base*HalfSourceBatchCopyVolume.batchControlUnit (P f p base) (len f p base))+
  W f p*(256*(p.L-p.m)+99)+32

variable (hm : p.m ≤ p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (a b : ℕ) (stored : GraphAdaptiveBatchSources.Stored f p)
  (hc : GraphAdaptiveBatchSources.Correct f p hm input a b stored)

 theorem root_bits : (GraphAdaptiveRootBatch.prepare f p hm input a b stored hc base).bitSteps ≤ bits f p base := by
  rw [GraphAdaptiveRootBatch.prepare_bits]
  have hh := Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
    HalfSourceBatchCopyVolume.actual_bits f p hm input a b stored hc (base.atSlot slot))
  change _≤∑ _slot : Fin (W f p),V f p base*BackendScalarBits.backendScalarUnit (H f p base).size at hh
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  simpa only [bits,Nat.mul_assoc] using hh

 theorem root_control (hB : 1 ≤ CompactBlocks.blockCount n h) :
    (GraphAdaptiveRootBatch.prepare f p hm input a b stored hc base).control ≤ control f p base := by
  rw [GraphAdaptiveRootBatch.prepare_control]
  have hh := Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
    HalfSourceBatchCopyVolume.actual_control f p hm input a b stored hc (base.atSlot slot) hB)
  change _≤∑ _slot : Fin (W f p),V f p base*HalfSourceBatchCopyVolume.batchControlUnit (P f p base) (len f p base) at hh
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  exact Nat.add_le_add_right (Nat.add_le_add_right hh _) _

omit a b stored hc in
theorem banks_bits (stored : GraphOwnBandPreparation.Stores f p (S:=S))
    (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a)) :
    (GraphOwnBandPreparation.banks f p hm input base stored hc).bitSteps ≤
      GraphOwnBandCollection.G f p (S:=S)*bits f p base := by
  apply tabulate_bits
  intro g
  exact root_bits f p (GraphOwnBandCollection.index f p base g) hm input _ _ _ _

omit a b stored hc in
theorem banks_control (stored : GraphOwnBandPreparation.Stores f p (S:=S))
    (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))
    (hB : 1 ≤ CompactBlocks.blockCount n h) :
    (GraphOwnBandPreparation.banks f p hm input base stored hc).control ≤
      GraphOwnBandCollection.G f p (S:=S)*(control f p base+64*(GraphOwnBandCollection.G f p (S:=S)).size^2+64)+8 := by
  apply tabulate_control
  intro g
  have hh := root_control f p (GraphOwnBandCollection.index f p base g) hm input
    (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val
    (GraphOwnBandRouter.decode (S:=S) (L:=p.L) (m:=p.m) g).1.val _ (hc _) hB
  dsimp only [GraphOwnBandPreparation.bank]
  exact Nat.add_le_add_right (Nat.add_le_add_right hh _) _

#print axioms root_bits
#print axioms root_control
#print axioms banks_bits
#print axioms banks_control
end ThinMatrix.GraphOwnBankCopyCosts
