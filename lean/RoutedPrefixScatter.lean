import PrefixBatchSchedule
import IndexedRowScatter

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThinMatrix.RoutedPrefixScatter
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open CappedBitPreparation (Key)
open GroupedPreparation (keyVector pairKeys)
open RectangularBatch (Scheme)
variable {P ell r C B A Z M U V : ℕ}

def entries (out : RoutedPrefixBatch.Result M C) : List (Fin M × Vector Cell C) :=
  List.ofFn (fun j : Fin out.indices.length =>
    (out.indices[j.val],out.output[j.val]'(by rw [out.size_eq];exact j.isLt)))

@[simp] theorem entries_length (out : RoutedPrefixBatch.Result M C) : (entries out).length=out.indices.length := by
  simp only [entries,List.length_ofFn]

theorem entries_mem (out : RoutedPrefixBatch.Result M C) (entry : Fin M × Vector Cell C) :
    entry∈entries out ↔ ∃ j : Fin out.indices.length,
      entry=(out.indices[j.val],out.output[j.val]'(by rw [out.size_eq];exact j.isLt)) := by
  simp only [entries,List.mem_ofFn]
  constructor <;> rintro ⟨j,hj⟩ <;> exact ⟨j,hj.symm⟩

@[simp] theorem entries_keys (out : RoutedPrefixBatch.Result M C) : (entries out).map Prod.fst=out.indices := by
  simp only [entries,List.map_ofFn]
  exact List.ofFn_getElem

def collect (out : Vector (Vector (RoutedPrefixBatch.Result M C) U) V) : Run (List (Fin M × Vector Cell C)) :=
  let rows := out.toList.flatMap (fun row => row.toList.flatMap entries)
  ⟨rows,0,64*rows.length+32*V*(U+1)+16⟩

theorem collect_mem (out : Vector (Vector (RoutedPrefixBatch.Result M C) U) V) (entry : Fin M × Vector Cell C) :
    entry∈(collect out).value ↔ ∃ a : Fin V, ∃ b : Fin U,
      entry∈entries ((out.get a).get b) := by
  simp only [collect,List.mem_flatMap]
  constructor
  · rintro ⟨row,hr,part,hp,he⟩
    obtain ⟨a,ha⟩ := List.mem_iff_get.mp hr
    obtain ⟨b,hb⟩ := List.mem_iff_get.mp hp
    refine ⟨Fin.cast (by simp) a,Fin.cast (by simp) b,?_⟩
    simpa only [Vector.get_eq_getElem,Fin.val_cast,←ha,←hb,List.get_eq_getElem,Vector.getElem_toList] using he
  · rintro ⟨a,b,he⟩
    refine ⟨out.get a,?_,(out.get a).get b,?_,he⟩
    · exact Vector.mem_toList_iff.mpr (Vector.getElem_mem a.isLt)
    · exact Vector.mem_toList_iff.mpr (Vector.getElem_mem b.isLt)

theorem collect_length (out : Vector (Vector (RoutedPrefixBatch.Result M C) U) V) :
    (collect out).value.length=∑ a : Fin V, ∑ b : Fin U, ((out.get a).get b).indices.length := by
  simp only [collect,List.length_flatMap,entries_length]
  have h (row : Vector (RoutedPrefixBatch.Result M C) U) :
      (List.map (fun z => z.indices.length) row.toList).sum=∑ b : Fin U,(row.get b).indices.length := by
    conv_lhs => rw [←Vector.ofFn_getElem (xs:=row),Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
    rfl
  simp only [h]
  conv_lhs => rw [←Vector.ofFn_getElem (xs:=out),Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  rfl

theorem collect_contains (out : Vector (Vector (RoutedPrefixBatch.Result M C) U) V)
    (a : Fin V) (b : Fin U) (j : Fin M) (hj : j∈((out.get a).get b).indices) :
    j∈(collect out).value.map Prod.fst := by
  rw [←entries_keys] at hj
  obtain ⟨entry,hm,he⟩ := List.mem_map.mp hj
  exact List.mem_map.mpr ⟨entry,(collect_mem out entry).mpr ⟨a,b,hm⟩,he⟩

def production (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (j : Fin requests.size) (col : Fin (B*C)) : ℤ :=
  let bc := finProdFinEquiv.symm col
  view ((PrefixCompletionProgram.row (xs.get bc.1) (PrefixCompletionMatrices.prepare (xs.get bc.1)).value
    requests[j.val]).value.output.get bc.2)

def rowView (row : Vector Cell C) : Fin C → ℤ := fun c => view (row.get c)

theorem schedule_covers (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (j : Fin requests.size) :
    j∈(collect (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests
      (RoutedPrefixBatch.prepare xs requests).value).value).value.map Prod.fst := by
  let pair := (PrefixRequestKey.locate (pairKeys ell) (PrefixRequestKey.pairPart requests[j.val])).value
  let idx := PrefixBatchSchedule.rank (PrefixRequestKey.prefixPart requests[j.val])
  apply collect_contains _ pair idx j
  simp only [PrefixBatchSchedule.execute_get,RoutedPrefixBatch.group]
  rw [RoutedPrefixBatch.ids_value]
  simp only [PrefixRequestRouting.selected,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  exact ⟨(PrefixBatchSchedule.digits_rank _).symm,(PrefixRequestKey.locate_get _ rfl _).symm⟩

theorem schedule_values (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (hk : ∀ b, (xs.get b).grouped.keys=keyVector ell r)
    (hp : ∀ b, (xs.get b).grouped.pairs=pairKeys ell)
    (requests : Array (Vector (Fin 4) (P+ell))) (entry : Fin requests.size × Vector Cell (B*C))
    (he : entry∈(collect (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests
      (RoutedPrefixBatch.prepare xs requests).value).value).value) :
    rowView entry.2=production xs requests entry.1 := by
  obtain ⟨pair,idx,hm⟩ := (collect_mem _ entry).mp he
  rw [PrefixBatchSchedule.execute_get] at hm
  obtain ⟨j,rfl⟩ := (entries_mem _ entry).mp hm
  funext col
  obtain ⟨⟨b,c⟩,rfl⟩ := finProdFinEquiv.surjective col
  simpa only [rowView,production,Equiv.symm_apply_apply,PrefixBlockBatch.column,RoutedPrefixBatch.group] using
    RoutedPrefixBatch.group_agrees scheme hv hD hA hZ hfirst hlast xs hk hp requests pair
      (PrefixBatchSchedule.digits idx) j b c

def execute (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) : Run (Vector (Vector Cell (B*C)) requests.size) :=
  let batches := PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests stored
  let rows := collect batches.value
  let blank := Vector.replicate (B*C) zero
  let initial := Vector.replicate requests.size blank
  let out := IndexedRowScatter.run rows.value initial
  ⟨out.value,batches.bitSteps+rows.bitSteps+out.bitSteps,
    batches.control+rows.control+out.control+32*(requests.size+B*C+1)⟩

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (hk : ∀ b, (xs.get b).grouped.keys=keyVector ell r)
    (hp : ∀ b, (xs.get b).grouped.pairs=pairKeys ell)
    (requests : Array (Vector (Fin 4) (P+ell))) (j : Fin requests.size) (b : Fin B) (c : Fin C) :
    view (((execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).value.get j).get
      (PrefixBlockBatch.column b c))=
      view ((PrefixCompletionProgram.row (xs.get b) (PrefixCompletionMatrices.prepare (xs.get b)).value
        requests[j.val]).value.output.get c) := by
  have hh := IndexedRowScatter.correct
    (collect (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests
      (RoutedPrefixBatch.prepare xs requests).value).value).value
    (Vector.replicate requests.size (Vector.replicate (B*C) zero)) rowView (production xs requests) j
    (schedule_values scheme hv hD hA hZ hfirst hlast xs hk hp requests)
    (schedule_covers scheme hD hA hZ hfirst hlast xs requests j)
  simpa only [execute,rowView,production,PrefixBlockBatch.column,Equiv.symm_apply_apply] using
    congrFun hh (PrefixBlockBatch.column b c)

theorem output_count (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (collect (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests
      (RoutedPrefixBatch.prepare xs requests).value).value).value.length=requests.size := by
  rw [collect_length]
  simp only [PrefixBatchSchedule.execute_get,RoutedPrefixBatch.group]
  exact PrefixBatchSchedule.ids_total xs requests

theorem bits (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : RoutedPrefixBatch.Prepared P ell r C B requests.size) :
    (execute scheme hD hA hZ hfirst hlast requests stored).bitSteps=
      (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests stored).bitSteps := by
  simp only [execute,IndexedRowScatter.bits,collect,add_zero]

theorem control (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (execute scheme hD hA hZ hfirst hlast requests (RoutedPrefixBatch.prepare xs requests).value).control=
      (PrefixBatchSchedule.execute scheme hD hA hZ hfirst hlast requests
        (RoutedPrefixBatch.prepare xs requests).value).control+
      128*requests.size+32*(2^ell)*(4^P+1)+32*(B*C)+52 := by
  have hn := output_count scheme hD hA hZ hfirst hlast xs requests
  simp only [collect] at hn
  simp only [execute,IndexedRowScatter.control,collect]
  rw [hn]
  ring

#print axioms entries_length
#print axioms entries_mem
#print axioms entries_keys
#print axioms collect_mem
#print axioms collect_length
#print axioms collect_contains
#print axioms schedule_covers
#print axioms schedule_values
#print axioms correct
#print axioms output_count
#print axioms bits
#print axioms control
end ThinMatrix.RoutedPrefixScatter
