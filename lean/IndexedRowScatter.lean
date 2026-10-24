import BinaryGroupedPreparation

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! Scatter retained row pointers to original occurrence indices. Every
retained row is written once; no search through a group's rows is used.
Scalar coefficient arrays are shared intact and index arithmetic is charged
as bounded indexed control, with binary-address refinement separate. -/
namespace ThinMatrix.IndexedRowScatter
open BinaryGroupedCoordinates
variable {V W : Type} {M : ℕ}

def run (rows : List (Fin M × V)) (initial : Vector V M) : Run (Vector V M) :=
  match rows with
  | [] => ⟨initial,0,4⟩
  | row::rest =>
    let out := run rest (initial.set row.1.val row.2 row.1.isLt)
    ⟨out.value,out.bitSteps,out.control+32⟩

theorem bits (rows : List (Fin M × V)) (initial : Vector V M) : (run rows initial).bitSteps=0 := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih => exact ih _

theorem control (rows : List (Fin M × V)) (initial : Vector V M) :
    (run rows initial).control=32*rows.length+4 := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih => simp only [run,ih,List.length_cons];omega

theorem preserves (rows : List (Fin M × V)) (initial : Vector V M) (view : V → W)
    (expected : Fin M → W) (query : Fin M)
    (hrows : ∀ row∈rows, view row.2=expected row.1)
    (hbefore : view (initial.get query)=expected query) :
    view ((run rows initial).value.get query)=expected query := by
  induction rows generalizing initial with
  | nil => exact hbefore
  | cons row rows ih =>
    apply ih _ (fun r hr => hrows r (List.mem_cons_of_mem _ hr))
    simp only [Vector.get_eq_getElem,Vector.getElem_set]
    split
    · rename_i h
      have heq : row.1=query := Fin.ext h
      simpa only [heq] using hrows row List.mem_cons_self
    · exact hbefore

theorem correct (rows : List (Fin M × V)) (initial : Vector V M) (view : V → W)
    (expected : Fin M → W) (query : Fin M)
    (hrows : ∀ row∈rows, view row.2=expected row.1)
    (hcover : query∈rows.map Prod.fst) :
    view ((run rows initial).value.get query)=expected query := by
  induction rows generalizing initial with
  | nil => simp at hcover
  | cons row rows ih =>
    have hr : ∀ r∈rows, view r.2=expected r.1 := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    simp only [List.map_cons,List.mem_cons] at hcover
    rcases hcover with hh|ht
    · apply preserves rows _ view expected query hr
      simp only [Vector.get_eq_getElem,Vector.getElem_set,hh,ite_true]
      simpa only [hh] using hrows row List.mem_cons_self
    · exact ih _ hr ht

theorem untouched (rows : List (Fin M × V)) (initial : Vector V M) (query : Fin M)
    (h : query∉rows.map Prod.fst) : (run rows initial).value.get query=initial.get query := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at h
    rw [show (run (row::rows) initial).value=(run rows (initial.set row.1.val row.2 row.1.isLt)).value from rfl,ih _ h.2]
    simp only [Vector.get_eq_getElem,Vector.getElem_set]
    split
    · rename_i hh; exact False.elim (h.1 (Fin.ext hh).symm)
    · rfl

#print axioms bits
#print axioms control
#print axioms preserves
#print axioms correct
#print axioms untouched
end ThinMatrix.IndexedRowScatter
