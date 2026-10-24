import GraphOwnRootSpec

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! The selected LOW product consumes two original-ID root arrays. It retains
one channel-weight computation and one residue projection, then evaluates
only the requested cyclic coefficient for every original occurrence/block.
All full cyclic source rows are still read and charged. -/
namespace ThinMatrix.GraphOwnRootProduct
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation ResidualFamilyKeys
open GoodMapEmbedding ExactHalfSourcePlan GroupedPreparation
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev C := (p.m+1)*f.cyclic
abbrev Rows := Vector (Vector Cell (B (n:=n) (h:=h)*C f p)) (M (n:=n))
abbrev Requests := Vector (GraphCompletionRequests.Physical p.L p.m f.cyclic) (M (n:=n))

def execute (ws : Vector Cell p.t) (channel : Channel p.m) (requests : Requests f p)
    (left right : Rows f p) : Run (Vector (Vector Cell (B (n:=n) (h:=h))) (M (n:=n))) :=
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  let counts := RetainedRootWindows.weights channel
  let residues := ofStoredFn requests (fun j => (requests.get j).coefficient)
  let result := SelectedRootRows.execute ws left right (counts.value.1+counts.value.2) residues
  ⟨result.value,counts.bitSteps+result.bitSteps,counts.control+16*M (n:=n)+result.control+16⟩

theorem card_eq (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (request : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    (RetainedRootWindows.weights ((GraphSharedTargets.keys f p).value.channels.get c)).value.1+
      (RetainedRootWindows.weights ((GraphSharedTargets.keys f p).value.channels.get c)).value.2=
      GraphWeightedRootProducts.card (GraphOwnRootSpec.graph f p input block request)
        (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target request)) := by
  rw [RetainedRootWindows.weights_value]
  rfl

attribute [local irreducible] GraphPrefixProgram.fromInputs

theorem correct (input : BinaryFoldedFormation.Inputs n) (u v : Fin (J p.m))
    (run : Fin (2*p.m+1)) (c : Fin (channelCount p.m p.t))
    (ws : Vector Cell p.t) (hw : ∀ d,view (ws.get d)=(TensorContraction.residualWeight (2*p.m) p.t d.val : ℤ))
    (channel : Channel p.m) (hc : channel=(GraphSharedTargets.keys f p).value.channels.get c)
    (requests : Requests f p) (hq : requests=(GraphSharedTargets.prepare f p input.target).physical.value)
    (left right : Rows f p)
    (hl : ∀ j block col,view ((left.get j).get (PrefixBlockBatch.column block col))=
      GraphOwnRootSpec.rootValue f p input u v run c false j block col)
    (hr : ∀ j block col,view ((right.get j).get (PrefixBlockBatch.column block col))=
      GraphOwnRootSpec.rootValue f p input u v run (GraphOwnRootSpec.transposed f p c).value true j block col)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    view (((execute f p ws channel requests left right).value.get j).get block)=
      GraphWeightedRootProducts.sourceValue (GraphOwnRootSpec.graph f p input block j)
        (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target j))
        input.target (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  simp only [execute,SelectedRootRows.execute_get,ofStoredFn_eq,Vector.get_ofFn,hc,hq]
  rw [card_eq f p input u v run c j block]
  apply GraphSelectedRootProduct.entry_value
  · exact hw
  · intro col
    rw [hl,GraphOwnRootSpec.rootValue_eq]
    rfl
  · intro col
    rw [hr,GraphOwnRootSpec.rootValue_eq,←GraphOwnRootSpec.right_index f p input u v run c j block]
    rfl
  · exact GraphOwnRootSpec.accepts f p input u v run c j block

theorem bits (ws : Vector Cell p.t) (channel : Channel p.m) (requests : Requests f p)
    (left right : Rows f p) (W A : ℕ)
    (hw : ∀ d,(view (ws.get d)).natAbs≤W)
    (hl : SelectedRootRows.RowsBound A left) (hr : SelectedRootRows.RowsBound A right) :
    (execute f p ws channel requests left right).bitSteps≤
      (RetainedRootWindows.weights channel).bitSteps+M (n:=n)*(B (n:=n) (h:=h)*SelectedRootProduct.bitBudget f.cyclic p.t W A) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact Nat.add_le_add_left (SelectedRootRows.execute_bits _ _ _ _ W A _ hw hl hr) _

theorem control (ws : Vector Cell p.t) (channel : Channel p.m) (requests : Requests f p)
    (left right : Rows f p) :
    (execute f p ws channel requests left right).control≤
      (RetainedRootWindows.weights channel).control+16*M (n:=n)+
        SelectedRootRows.controlBudget (p.m+1) f.cyclic p.t (B (n:=n) (h:=h)) (M (n:=n))+16 := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  exact Nat.add_le_add_right (Nat.add_le_add_left (SelectedRootRows.execute_control _ _ _ _ _) _) _

#print axioms card_eq
#print axioms correct
#print axioms bits
#print axioms control
end ThinMatrix.GraphOwnRootProduct
