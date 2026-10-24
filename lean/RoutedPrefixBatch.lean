import PrefixBlockBatch
import PrefixRequestRouting

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Retained production prefix matrices and a single request router feed
compatible block batches. Group outputs keep their original occurrence IDs;
the per-row theorem refines the existing elementary production row. All B*C
columns are retained. The enclosing graph/window scheduler and its optimized
rounded asymptotic ledger are not asserted by this module. -/
namespace ThinMatrix.RoutedPrefixBatch
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open CappedBitPreparation (Key)
open GroupedPreparation (keyVector pairKeys)
open RectangularBatch (Scheme)

variable {P ell r C B A Z M : ℕ}

structure Prepared (P ell r C B M : ℕ) where
  sources : Vector (CappedPrefixProgram.Prepared P ell r C) B
  banks : PrefixBlockBatch.Banks P ell r C B
  keys : Vector (Key ell) (CappedSubsetList.count ell r)
  pairs : Vector (Key ell) (2^ell)
  router : BooleanRequestRouter.Tree (Fin M) (P+(P+ell))

def prepare (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) : Run (Prepared P ell r C B requests.size) :=
  let banks := PrefixBlockBatch.prepare xs
  let routing := PrefixRequestRouting.run requests
  let keys := GroupedPreparation.storeKeys ell r
  let pairs := GroupedPreparation.storePairs ell
  ⟨⟨xs,banks.value,keys.value,pairs.value,routing.value⟩,
    banks.bitSteps+routing.bitSteps,banks.control+routing.control+keys.work+pairs.work+16⟩

def ids (stored : Prepared P ell r C B M) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    Run (List (Fin M)) :=
  let key := PrefixRequestRouting.code digits (stored.pairs.get pair)
  let out := BooleanRequestRouter.read stored.router key
  ⟨out.value,out.bitSteps,out.control+32*(P+ell+1)⟩

theorem prepare_bits (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hx : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (prepare xs requests).bitSteps≤B*(2^ell*PrefixCompletionMatrices.bitBudget P (CappedSubsetList.count ell r) C H) := by
  simpa only [prepare,(PrefixRequestRouting.run_cost requests).1,add_zero] using
    PrefixBlockBatch.prepare_bits xs H hx

theorem prepare_control (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) :
    (prepare xs requests).control≤
      B*(2^ell*(PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C+32)+40)+
      12*2^(P+(P+ell))+requests.size*(16*(P+(P+ell)+1)^2+64*(P+ell+1)+36)+
      GroupedPreparation.keyBudget ell r+GroupedPreparation.keyBudget ell ell+46 := by
  have hb := PrefixBlockBatch.prepare_control xs
  have hr := (PrefixRequestRouting.run_cost requests).2
  have hk := GroupedPreparation.storeKeys_work ell r
  have hp := GroupedPreparation.storePairs_work ell
  simp only [prepare]
  omega

theorem ids_control (stored : Prepared P ell r C B M) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (ids stored pair digits).control≤16*(P+(P+ell)+1)^2+32*(P+ell+1) :=
  Nat.add_le_add_right (BooleanRequestRouter.read_control stored.router
    (PrefixRequestRouting.code digits (stored.pairs.get pair))) _

theorem ids_value (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (ids (prepare xs requests).value pair digits).value=
      PrefixRequestRouting.selected requests digits ((pairKeys ell).get pair) := by
  simp only [ids,prepare,GroupedPreparation.storePairs_value,BooleanRequestRouter.read_value,
    PrefixRequestRouting.run_bucket]

theorem ids_match (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (i : Fin requests.size) (hi : i∈(ids (prepare xs requests).value pair digits).value) :
    PrefixRequestKey.prefixPart requests[i.val]=digits ∧
      PrefixRequestKey.pairPart requests[i.val]=(pairKeys ell).get pair := by
  rw [ids_value] at hi
  simpa only [PrefixRequestRouting.selected,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] using hi

def actives (requests : Array (Vector (Fin 4) (P+ell))) (indices : List (Fin requests.size)) :
    GroupedPreparation.Counted (Array (Key ell)) :=
  ⟨indices.toArray.map (fun i => PrefixRequestKey.activePart requests[i.val]),
    indices.length*(16*ell+16)+4⟩

@[simp] theorem actives_size (requests : Array (Vector (Fin 4) (P+ell))) (indices : List (Fin requests.size)) :
    (actives requests indices).value.size=indices.length := by simp [actives]

theorem actives_get (requests : Array (Vector (Fin 4) (P+ell))) (indices : List (Fin requests.size))
    (j : Fin indices.length) :
    (actives requests indices).value[j.val]'(by simp)=PrefixRequestKey.activePart requests[(indices[j.val]).val] := by
  simp [actives]

structure Result (M C : ℕ) where
  indices : List (Fin M)
  output : Array (Vector Cell C)
  size_eq : output.size=indices.length

def group (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell)))
    (stored : Prepared P ell r C B requests.size)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) : Run (Result requests.size (B*C)) :=
  let selected := ids stored pair digits
  let masks := actives requests selected.value
  let out := PrefixBlockBatch.complete scheme hD hA hZ hfirst hlast
    stored.keys stored.banks pair digits masks.value
  ⟨⟨selected.value,out.value,by simp [out,masks]⟩,
    selected.bitSteps+out.bitSteps,selected.control+masks.work+out.control+12⟩

theorem pair_locate (pair : Fin (2^ell)) :
    (PrefixRequestKey.locate (pairKeys ell) ((pairKeys ell).get pair)).value=pair := by
  have hh := PrefixRequestKey.locate_get (pairKeys ell) rfl ((pairKeys ell).get pair)
  have hi := (GroupedPreparation.pairKeys_nodup ell).getElem_inj_iff
    (i:=(PrefixRequestKey.locate (pairKeys ell) ((pairKeys ell).get pair)).value.val) (j:=pair.val)
    (hi:=by rw [Vector.length_toList]; exact (PrefixRequestKey.locate (pairKeys ell) ((pairKeys ell).get pair)).value.isLt)
    (hj:=by rw [Vector.length_toList]; exact pair.isLt)
  apply Fin.ext
  apply hi.mp
  simpa only [Vector.getElem_toList,Vector.get_eq_getElem] using hh

theorem group_value (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (hk : ∀ b, (xs.get b).grouped.keys=keyVector ell r)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (j : Fin (ids (prepare xs requests).value pair digits).value.length) (b : Fin B) (c : Fin C) :
    view (((group scheme hD hA hZ hfirst hlast requests (prepare xs requests).value pair digits).value.output[j.val]'(by simp [group])).get
      (PrefixBlockBatch.column b c))=
      CappedPrefixProgram.query (xs.get b) pair digits.get
        (CappedBitPreparation.support (PrefixRequestKey.activePart
          requests[((ids (prepare xs requests).value pair digits).value[j.val]).val])) c := by
  have hh := PrefixBlockBatch.complete_value scheme hv hD hA hZ hfirst hlast xs (keyVector ell r) hk pair digits
    (actives requests (ids (prepare xs requests).value pair digits).value).value
    ⟨j.val,by rw [actives_size];exact j.isLt⟩ b c
  rw [actives_get] at hh
  simpa only [group,prepare,GroupedPreparation.storeKeys_value] using hh

/-- Each batch result equals the existing production row at its original
occurrence index, including duplicates and all block/coefficient columns. -/
theorem group_agrees (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (hk : ∀ b, (xs.get b).grouped.keys=keyVector ell r)
    (hp : ∀ b, (xs.get b).grouped.pairs=pairKeys ell)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (j : Fin (ids (prepare xs requests).value pair digits).value.length) (b : Fin B) (c : Fin C) :
    view (((group scheme hD hA hZ hfirst hlast requests (prepare xs requests).value pair digits).value.output[j.val]'(by simp [group])).get
      (PrefixBlockBatch.column b c))=
      view ((PrefixCompletionProgram.row (xs.get b) (PrefixCompletionMatrices.prepare (xs.get b)).value
        requests[((ids (prepare xs requests).value pair digits).value[j.val]).val]).value.output.get c) := by
  rw [group_value scheme hv hD hA hZ hfirst hlast xs hk,PrefixCompletionProgram.row_value]
  have hi := ids_match xs requests pair digits _ (List.getElem_mem j.isLt)
  simp only [PrefixRequestKey.make,hp b,hi.1,hi.2,pair_locate]

theorem group_bits (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hH : 1≤H) (hx : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (requests : Array (Vector (Fin 4) (P+ell))) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (group scheme hD hA hZ hfirst hlast requests (prepare xs requests).value pair digits).bitSteps≤
      CompactBlocks.blockCount (ids (prepare xs requests).value pair digits).value.length A*
        CompactBlocks.blockCount (B*C) Z*RectangularBatch.scalarBudget scheme (CappedSubsetList.count ell r) H := by
  have hh := PrefixBlockBatch.complete_bits scheme hD hA hZ hfirst hlast xs (keyVector ell r) H hH hx pair digits
    (actives requests (ids (prepare xs requests).value pair digits).value).value
  simpa only [group,prepare,GroupedPreparation.storeKeys_value,actives_size,ids,BooleanRequestRouter.read_bits,zero_add] using hh

theorem group_control (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (requests : Array (Vector (Fin 4) (P+ell))) (stored : Prepared P ell r C B requests.size)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (group scheme hD hA hZ hfirst hlast requests stored pair digits).control≤
      (PrefixBlockBatch.complete scheme hD hA hZ hfirst hlast stored.keys stored.banks pair digits
        (actives requests (ids stored pair digits).value).value).control+
      16*(P+(P+ell)+1)^2+32*(P+ell+1)+(ids stored pair digits).value.length*(16*ell+16)+16 := by
  have hi := ids_control stored pair digits
  simp only [group,actives]
  omega

/-- Source preparation itself establishes the common selector/key layout. -/
theorem source_layout (sources : Vector (RetainedCappedGroups.Source P ell C) B) (b : Fin B) :
    ((sources.map (fun X => (CappedPrefixProgram.execute r X).value)).get b).grouped.keys=keyVector ell r ∧
    ((sources.map (fun X => (CappedPrefixProgram.execute r X).value)).get b).grouped.pairs=pairKeys ell := by
  simp only [Vector.get_map,CappedPrefixProgram.execute,RetainedCappedGroups.prepare,
    GroupedPreparation.storeKeys_value,GroupedPreparation.storePairs_value,and_self]

/-- No extra hypothesis about intermediate prefix leaves is needed for
produced sources: their height follows from the original coefficient cap. -/
theorem source_bound (sources : Vector (RetainedCappedGroups.Source P ell C) B)
    (H : ℕ) (hH : ∀ b, OppositeWindowLayer.Bound (sources.get b) H) (b : Fin B) (pair : Fin (2^ell)) :
    PrefixCompletionMatrices.LeafBound
      (((sources.map (fun X => (CappedPrefixProgram.execute r X).value)).get b).traces.get pair) (2^P*H) := by
  intro j q c
  simpa only [Vector.get_map] using CappedPrefixProgram.output_bound r (sources.get b) H (hH b) pair j q c

#print axioms ids_value
#print axioms prepare_bits
#print axioms prepare_control
#print axioms ids_control
#print axioms ids_match
#print axioms actives_size
#print axioms actives_get
#print axioms pair_locate
#print axioms group_value
#print axioms group_agrees
#print axioms group_bits
#print axioms group_control
#print axioms source_layout
#print axioms source_bound
end ThinMatrix.RoutedPrefixBatch
