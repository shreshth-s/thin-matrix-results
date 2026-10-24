import IndexedRowScatter
import FiniteRequestRouter

set_option autoImplicit false
set_option maxHeartbeats 1400000

/-! Collect a partition of completed request rows using their original IDs.
There is one output array for the entire side, not one padded output per
opposite band. Every selected row is copied once and duplicates in the user's
request list remain separate indexed occurrences. -/
namespace ThinMatrix.OriginalRowCollection
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators
variable {M C G : ℕ}

structure Rows (M C : ℕ) where
  indices : List (Fin M)
  values : Vector (Vector Cell C) indices.length

def tag (rows : Rows M C) : List (Fin M × Vector Cell C) :=
  List.ofFn (fun i => (rows.indices[i.val],rows.values.get i))

def flatten (children : Vector (Rows M C) G) : List (Fin M × Vector Cell C) :=
  (List.ofFn (fun g => tag (children.get g))).flatten

@[simp] theorem tag_length (rows : Rows M C) : (tag rows).length=rows.indices.length := by
  simp only [tag,List.length_ofFn]

theorem flatten_length (children : Vector (Rows M C) G) :
    (flatten children).length=∑ g : Fin G,(children.get g).indices.length := by
  simp only [flatten,List.length_flatten,List.map_ofFn,Function.comp_apply,tag_length,List.sum_ofFn]

def execute (child : Fin G → Run (Rows M C)) : Run (Vector (Vector Cell C) M) :=
  let children := tabulate (Vector.replicate G ()) child
  let rows := flatten children.value
  let out := IndexedRowScatter.run rows (Vector.replicate M (Vector.replicate C BinaryCell.zero))
  ⟨out.value,children.bitSteps+out.bitSteps,
    children.control+out.control+32*rows.length+16*G+16*(M+C)+24⟩

theorem flatten_mem (children : Vector (Rows M C) G) (entry : Fin M × Vector Cell C) :
    entry∈flatten children ↔ ∃ g : Fin G, ∃ j : Fin (children.get g).indices.length,
      entry=((children.get g).indices[j.val],(children.get g).values.get j) := by
  simp only [flatten,List.mem_flatten,List.mem_ofFn]
  constructor
  · rintro ⟨xs,⟨g,rfl⟩,hj⟩
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hj
    exact ⟨g,j,hj.symm⟩
  · rintro ⟨g,j,rfl⟩
    exact ⟨tag (children.get g),⟨g,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

theorem correct (child : Fin G → Run (Rows M C)) (expected : Fin M → Fin C → ℤ)
    (hrow : ∀ g j c,view ((((child g).value.values.get j).get c))=
      expected ((child g).value.indices[j.val]) c)
    (hcover : ∀ i : Fin M,∃ g : Fin G,i∈(child g).value.indices) (i : Fin M) (c : Fin C) :
    view (((execute child).value.get i).get c)=expected i c := by
  have hrow' (g : Fin G) (xs : Rows M C) (he : xs=(child g).value)
      (j : Fin xs.indices.length) : view ((xs.values.get j).get c)=expected xs.indices[j.val] c := by
    subst xs
    exact hrow g j c
  dsimp only [execute]
  apply IndexedRowScatter.correct _ _ (fun row : Vector Cell C => view (row.get c)) (fun i => expected i c) i
  · intro row hr
    obtain ⟨g,j,hj⟩ := (flatten_mem _ _).mp hr
    subst row
    exact hrow' g _ (tabulate_get _ _ g) j
  · obtain ⟨g,hi⟩ := hcover i
    obtain ⟨j,hj,hval⟩ := List.getElem_of_mem hi
    apply List.mem_map.mpr
    refine ⟨(i,(child g).value.values.get ⟨j,hj⟩),?_,rfl⟩
    apply List.mem_flatten.mpr
    refine ⟨tag (child g).value,?_,?_⟩
    · exact List.mem_ofFn.mpr ⟨g,congrArg tag (tabulate_get _ _ g)⟩
    · apply List.mem_ofFn.mpr
      refine ⟨⟨j,hj⟩,?_⟩
      simp only [hval]

/-- Source partition coverage comes from the actual retained router keys. -/
theorem selected_cover (keys : Vector (Fin G) M) (i : Fin M) :
    ∃ g : Fin G,i∈FiniteRequestRouter.selected keys g := by
  refine ⟨keys.get i,?_⟩
  simp [FiniteRequestRouter.selected]

theorem bits (child : Fin G → Run (Rows M C)) :
    (execute child).bitSteps=∑ g : Fin G,(child g).bitSteps := by
  simp only [execute,IndexedRowScatter.bits,Nat.add_zero,tabulate_bits_eq]

theorem control (child : Fin G → Run (Rows M C))
    (htotal : (∑ g : Fin G,(child g).value.indices.length)=M) :
    (execute child).control=(∑ g : Fin G,(child g).control)+48*G+80*M+16*C+36 := by
  have hlen : (flatten (tabulate (Vector.replicate G ()) child).value).length=M := by
    rw [flatten_length]
    simpa only [tabulate_get] using htotal
  simp only [execute,IndexedRowScatter.control,tabulate_control_eq,hlen]
  ring

#print axioms tag_length
#print axioms flatten_length
#print axioms flatten_mem
#print axioms correct
#print axioms selected_cover
#print axioms bits
#print axioms control
end ThinMatrix.OriginalRowCollection
