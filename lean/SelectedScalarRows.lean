import OriginalRowCollection
import RootProductCollection

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ThinMatrix.SelectedScalarRows
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators
variable {M S : ℕ}

def get (ids : List (Fin M)) (v : Vector Cell ids.length) (j : Fin ids.length) : Vector Cell 1 :=
  Vector.replicate 1 (v.get j)

/-- Sum retained scalar children before scattering one value per original ID. -/
def execute (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S) :
    Run (OriginalRowCollection.Rows M 1) :=
  let rows := tabulate (Vector.replicate ids.length ()) (RootProductCollection.sumRow values (get ids))
  let out := Vector.ofFn (fun j => (rows.value.get j).output)
  ⟨⟨ids,out⟩,rows.bitSteps,rows.control+16*ids.length+16*S+8⟩

@[simp] theorem indices (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S) :
    (execute ids values).value.indices=ids := rfl

theorem value (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S)
    (j : Fin ids.length) (c : Fin 1) :
    view ((((execute ids values).value.values.get j).get c))=∑ s,view ((values.get s).get j) := by
  simp only [execute,Vector.get_ofFn,tabulate_get,RootProductCollection.sumRow_value,get,Vector.get_replicate]

theorem bound (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S)
    (A : ℕ) (hA : ∀ s j,(view ((values.get s).get j)).natAbs≤A)
    (j : Fin ids.length) (c : Fin 1) :
    (view ((((execute ids values).value.values.get j).get c))).natAbs≤S*A := by
  simp only [execute,Vector.get_ofFn,tabulate_get]
  apply RootProductCollection.sumRow_bound _ _ A
  intro s i r
  simpa only [get,Vector.get_replicate] using hA s i

theorem bits (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S)
    (A : ℕ) (hA : ∀ s j,(view ((values.get s).get j)).natAbs≤A) :
    (execute ids values).bitSteps≤ ids.length*(S*BackendScalarBits.backendScalarUnit (S*A).size) := by
  apply tabulate_bits
  intro j
  simpa only [Nat.one_mul] using RootProductCollection.sumRow_bits values (get ids) A
    (fun s i _ => by simpa only [get,Vector.get_replicate] using hA s i) j

theorem control (ids : List (Fin M)) (values : Vector (Vector Cell ids.length) S) :
    (execute ids values).control≤ ids.length*(80*S+63)+16*S+16 := by
  have hh := tabulate_control (Vector.replicate ids.length ()) (RootProductCollection.sumRow values (get ids))
    (fun i => RootProductCollection.sumRow_control values (get ids) i)
  dsimp only [execute]
  norm_num at hh
  nlinarith only [hh]

#print axioms indices
#print axioms value
#print axioms bound
#print axioms bits
#print axioms control
end ThinMatrix.SelectedScalarRows
