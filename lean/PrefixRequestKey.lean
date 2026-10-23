import PrefixCompletionMatrices

set_option autoImplicit false

/-! Executable request decomposition. The pair lookup scans the retained pair
keys; its full linear scan is charged as indexed work, with no fast lookup or
binary-control assumption. Prefix and suffix keys are materialized vectors. -/
namespace ThinMatrix.PrefixRequestKey
open BinaryGroupedCoordinates BinaryGroupedPreparation CappedBitPreparation GroupedPreparation
open scoped BigOperators

def pairBit (q : Fin 4) : Bool := decide (2≤q.val)
def activeBit (q : Fin 4) : Bool := q.val%2==0

theorem local_form (q : Fin 4) (a : Fin 3) :
    CroppedGroupedSuffix.localForm (pairBit q) (activeBit q) a=BinaryPrefixContraction.form q a := by
  fin_cases q <;> fin_cases a <;> decide

theorem pair_mem {ell : ℕ} (key : Key ell) : key∈(pairKeys ell).toList := by
  rw [pairKeys_toList,mem_generate]
  rw [← support_card]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)

def locate {ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (key : Key ell) : Counted (Fin (2^ell)) :=
  let i := pairs.toList.idxOf key
  ⟨⟨if h : i<2^ell then i else 0,by split <;> (try assumption); exact pow_pos (by decide) _⟩,
    (8*ell+16)*pairs.toArray.size+8⟩

theorem locate_get {ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (hp : pairs=pairKeys ell) (key : Key ell) :
    pairs.get (locate pairs key).value=key := by
  have hm : key∈pairs.toList := by rw [hp]; exact pair_mem key
  have hi : pairs.toList.idxOf key<2^ell := by simpa using List.idxOf_lt_length_iff.mpr hm
  simp only [locate,hi,↓reduceDIte]
  have h := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hm)
  simpa only [Vector.getElem_toList,Vector.get_eq_getElem] using h

def locateBudget (ell : ℕ) : ℕ := (8*ell+16)*2^ell+8

theorem locate_work {ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (key : Key ell) :
    (locate pairs key).work=locateBudget ell := by simp [locate,locateBudget]

structure Request (P ell : ℕ) where
  prefixDigits : Vector (Fin 4) P
  pair : Fin (2^ell)
  active : Key ell

def prefixPart {P ell : ℕ} (labels : Vector (Fin 4) (P+ell)) : Vector (Fin 4) P :=
  Vector.ofFn (fun i => labels.get (Fin.castAdd ell i))
def pairPart {P ell : ℕ} (labels : Vector (Fin 4) (P+ell)) : Key ell :=
  Vector.ofFn (fun i => pairBit (labels.get (Fin.natAdd P i)))
def activePart {P ell : ℕ} (labels : Vector (Fin 4) (P+ell)) : Key ell :=
  Vector.ofFn (fun i => activeBit (labels.get (Fin.natAdd P i)))

def make {P ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (labels : Vector (Fin 4) (P+ell)) : Counted (Request P ell) :=
  let pair := locate pairs (pairPart labels)
  ⟨⟨prefixPart labels,pair.value,activePart labels⟩,pair.work+16*(P+ell)+16⟩

def makeBudget (P ell : ℕ) : ℕ := locateBudget ell+16*(P+ell)+16

theorem make_work {P ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (labels : Vector (Fin 4) (P+ell)) :
    (make pairs labels).work=makeBudget P ell := by simp [make,locate_work,makeBudget]

theorem make_forms {P ell : ℕ} (pairs : Vector (Key ell) (2^ell)) (hp : pairs=pairKeys ell)
    (labels : Vector (Fin 4) (P+ell)) :
    Fin.append (fun i => BinaryPrefixContraction.form ((make pairs labels).value.prefixDigits.get i))
      (fun i => CroppedGroupedSuffix.localForm ((pairKeys ell).get (make pairs labels).value.pair |>.get i)
        (decide (i∈support (make pairs labels).value.active)))=
      (fun i => BinaryPrefixContraction.form (labels.get i)) := by
  have hpair := locate_get pairs hp (pairPart labels)
  have hpair' := (congrArg (fun v : Vector (Key ell) (2^ell) => v.get (locate pairs (pairPart labels)).value) hp).symm.trans hpair
  funext i a
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [make,prefixPart]
  · simp only [Fin.append_right]
    change CroppedGroupedSuffix.localForm (R:=ℤ)
      (((pairKeys ell).get (locate pairs (pairPart labels)).value).get j)
      (decide (j∈support (activePart labels))) a=_
    rw [hpair']
    simp only [pairPart,activePart,Vector.get_ofFn,mem_support,Bool.decide_eq_true]
    exact local_form _ _

#print axioms local_form
#print axioms pair_mem
#print axioms locate_get
#print axioms locate_work
#print axioms make_work
#print axioms make_forms
end ThinMatrix.PrefixRequestKey
