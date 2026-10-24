import GraphOwnBandRuntimeCompletion
import GraphOwnBandPreparation

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThinMatrix.GraphOwnBandRuntimePreparation
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation GraphAdaptiveRootBatch
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (shape : GraphOwnBandRuntime.Shape p.L p.m)
  (hm : p.m≤p.L-p.m) (input : BinaryFoldedFormation.Inputs n)
  (base : Index f p) (stored : GraphOwnBandPreparation.Stores f p (S:=S))
  (hc : ∀ a : Fin S,GraphAdaptiveBatchSources.Correct f p hm input a.val a.val (stored.get a))

def bank (g : Fin (GraphOwnBandCollection.G f p (S:=S))) : Run (Prepared f p base) :=
  let a := (GraphOwnBandRuntime.decode shape g).1
  let out := GraphAdaptiveRootBatch.prepare f p hm input a.val a.val (stored.get a) (hc a)
    (GraphOwnBandRuntimeCompletion.index f p shape base g)
  ⟨⟨out.value.banks,out.value.layouts⟩,out.bitSteps,
    out.control+64*(GraphOwnBandRuntime.groups shape S).size^2+32⟩

 theorem bank_eq (g : Fin (GraphOwnBandCollection.G f p (S:=S))) :
    bank f p shape hm input base stored hc g=GraphOwnBandPreparation.bank f p hm input base stored hc g := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

/-- Allocate using the retained mask count, then erase the shape equality. -/
def banks : Run (GraphOwnBandPreparation.BankRows f p base (S:=S)) :=
  let out := tabulate (Vector.replicate (GraphOwnBandRuntime.groups shape S) ())
    (fun g => bank f p shape hm input base stored hc (Fin.cast (GraphOwnBandRuntime.groups_eq shape) g))
  ⟨out.value.cast (GraphOwnBandRuntime.groups_eq shape),out.bitSteps,out.control⟩

 theorem banks_eq : banks f p shape hm input base stored hc=GraphOwnBandPreparation.banks f p hm input base stored hc := by
  simp only [banks,bank_eq]
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

#print axioms bank_eq
#print axioms banks_eq
end ThinMatrix.GraphOwnBandRuntimePreparation
