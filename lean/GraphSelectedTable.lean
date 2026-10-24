import GraphSelectedIncidences

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Controller-facing nonnegative counts preserve the computed binary cells.
The caller supplies the retained producer's literal work; wrapping charges
reindexing, output copies and every table slot, without decoding to integers. -/
namespace ThinMatrix.GraphSelectedTable
open BinaryCell BinaryGroupedCoordinates
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
variable {α : Type} (input : BinaryFoldedFormation.Inputs n)
  (values : GraphSelectedIncidences.Values (n:=n) (h:=h))
  (hv : ∀ j b,view (BinaryLowHighNormalize.output values j b)=FoldedRequestBounds.count f b input j)

structure Payload (α : Type) (n h : ℕ) where
  source : α
  cells : Run (Vector Cell (EndToEndAPSP.incidenceSize n h))

/-- The prior-work field is an explicit composition input, not a proved
bound or a replacement for the concrete producer's cost theorem. -/
def execute (source : α) (priorWork addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (Payload α n h) :=
  let cells := GraphSelectedIncidences.execute values
  let wrapped := BinaryControllerExecution.Table.fromCells cells.value
    (GraphSelectedIncidences.nonnegative f input values hv) (⟨source,cells⟩ : Payload α n h) 0
  { wrapped.value with work := priorWork+cells.bitSteps+wrapped.bitSteps+
      (addressPrice+1)*(cells.control+wrapped.controlSites+8) }

theorem get (source : α) (priorWork addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    ((execute f input values hv source priorWork addressPrice).counts.get i).cell=
      (GraphSelectedIncidences.execute values).value.get i :=
  BinaryControllerExecution.Table.fromCells_get _ _ _ _ _

theorem correct (hh : 0<h) (source : α) (priorWork addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((execute f input values hv source priorWork addressPrice).counts.get i)=
      (EndToEndAPSP.flatInstance (h:=h) (BinaryFoldedFormation.viewTable input.left)
        (BinaryFoldedFormation.viewTable input.right) (BinaryFoldedFormation.viewTable input.target)).modCount r i := by
  unfold BinaryControllerExecution.nview
  rw [get]
  exact GraphSelectedIncidences.modCount f hh input values hv i

theorem count_bound (source : α) (priorWork addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((execute f input values hv source priorWork addressPrice).counts.get i)≤h := by
  unfold BinaryControllerExecution.nview
  rw [get]
  have hb := GraphSelectedIncidences.bound f input values hv i
  cases he : view ((GraphSelectedIncidences.execute values).value.get i) with
  | ofNat k =>
    rw [he] at hb
    exact hb
  | negSucc k => simp only [Int.toNat_negSucc]; exact Nat.zero_le _

theorem wrap_bits_zero {I : ℕ} (cells : Vector Cell I) (hn : ∀ i,0≤view (cells.get i)) (source : α) :
    (BinaryControllerExecution.Table.fromCells cells hn source 0).bitSteps=0 :=
  BinaryControllerExecution.tabulate_zero_bits _ (fun _=>rfl)

theorem work (source : α) (priorWork addressPrice : ℕ) :
    (execute f input values hv source priorWork addressPrice).work≤priorWork+
      EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
      (addressPrice+1)*(EndToEndAPSP.incidenceSize n h*
        (64*(EndToEndAPSP.incidenceSize n h).size^2+54)+21) := by
  have hc := GraphSelectedIncidences.control values
  have hb := GraphSelectedIncidences.bits values (fun j b => by
    rw [hv]; exact FoldedRequestBounds.count_bound f b input j)
  have hw := BinaryControllerExecution.Table.fromCells_control
    (GraphSelectedIncidences.execute values).value
    (GraphSelectedIncidences.nonnegative f input values hv)
    (⟨source,GraphSelectedIncidences.execute values⟩ : Payload α n h) 0
  unfold execute
  dsimp only
  rw [wrap_bits_zero]
  calc
    _ ≤ priorWork+EndToEndAPSP.incidenceSize n h*BackendScalarBits.backendScalarUnit h.size+
      (addressPrice+1)*(EndToEndAPSP.incidenceSize n h*
        (64*(EndToEndAPSP.incidenceSize n h).size^2+40)+8+(14*EndToEndAPSP.incidenceSize n h+5)+8) := by
      simp only [Nat.add_zero]
      exact Nat.add_le_add (Nat.add_le_add_left hb priorWork)
        (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

#print axioms get
#print axioms correct
#print axioms count_bound
#print axioms wrap_bits_zero
#print axioms work
end ThinMatrix.GraphSelectedTable
