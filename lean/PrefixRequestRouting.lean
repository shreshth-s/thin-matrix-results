import BooleanRequestRouter
import PrefixRequestKey

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Production ordinary labels route by their actual prefix digits and suffix
pair bits. The original occurrence index is the payload, so identical labels
are retained separately and can be scattered to their original positions.
The routing program never scans the retained pair-key list per request. -/
namespace ThinMatrix.PrefixRequestRouting
open BinaryGroupedCoordinates
open CappedBitPreparation (Key)

variable {P ell : ℕ}

def code (digits : Vector (Fin 4) P) (pair : Key ell) : BooleanRequestRouter.Key (P+(P+ell)) :=
  Vector.ofFn (Fin.append (fun i => PrefixRequestKey.pairBit (digits.get i))
    (Fin.append (fun i => PrefixRequestKey.activeBit (digits.get i)) pair.get))

theorem code_get (digits : Vector (Fin 4) P) (pair : Key ell) :
    (code digits pair).get=Fin.append (fun i => PrefixRequestKey.pairBit (digits.get i))
      (Fin.append (fun i => PrefixRequestKey.activeBit (digits.get i)) pair.get) := by
  funext i
  exact Vector.get_ofFn _ _

theorem digit_injective (a b : Fin 4) :
    PrefixRequestKey.pairBit a=PrefixRequestKey.pairBit b →
    PrefixRequestKey.activeBit a=PrefixRequestKey.activeBit b → a=b := by
  fin_cases a <;> fin_cases b <;> decide

theorem code_eq_iff (digits other : Vector (Fin 4) P) (pair otherPair : Key ell) :
    code digits pair=code other otherPair ↔ digits=other ∧ pair=otherPair := by
  constructor
  · intro h
    have hf := congrArg (fun v : BooleanRequestRouter.Key (P+(P+ell)) => v.get) h
    rw [code_get,code_get] at hf
    constructor
    · apply Vector.ext
      intro i hi
      apply digit_injective
      · have hh := congrFun hf (Fin.castAdd (P+ell) ⟨i,hi⟩)
        simpa only [Fin.append_left,Vector.get_eq_getElem] using hh
      · have hh := congrFun hf (Fin.natAdd P (Fin.castAdd ell ⟨i,hi⟩))
        simpa only [Fin.append_right,Fin.append_left,Vector.get_eq_getElem] using hh
    · apply Vector.ext
      intro i hi
      have hh := congrFun hf (Fin.natAdd P (Fin.natAdd P ⟨i,hi⟩))
      simpa only [Fin.append_right,Vector.get_eq_getElem] using hh
  · rintro ⟨rfl,rfl⟩; rfl

def address (labels : Vector (Fin 4) (P+ell)) :
    GroupedPreparation.Counted (BooleanRequestRouter.Key (P+(P+ell))) :=
  ⟨code (PrefixRequestKey.prefixPart labels) (PrefixRequestKey.pairPart labels),
    64*(P+ell+1)⟩

theorem address_eq_iff (labels : Vector (Fin 4) (P+ell))
    (digits : Vector (Fin 4) P) (pair : Key ell) :
    (address labels).value=code digits pair ↔
      PrefixRequestKey.prefixPart labels=digits ∧ PrefixRequestKey.pairPart labels=pair :=
  code_eq_iff _ _ _ _

def rows (requests : Array (Vector (Fin 4) (P+ell))) :
    List (BooleanRequestRouter.Key (P+(P+ell)) × Fin requests.size) :=
  List.ofFn (fun i => ((address requests[i.val]).value,i))

def run (requests : Array (Vector (Fin 4) (P+ell))) :
    Run (BooleanRequestRouter.Tree (Fin requests.size) (P+(P+ell))) :=
  let out := BooleanRequestRouter.build (rows requests)
  ⟨out.value,out.bitSteps,out.control+requests.size*(64*(P+ell+1)+24)+8⟩

def selected (requests : Array (Vector (Fin 4) (P+ell)))
    (digits : Vector (Fin 4) P) (pair : Key ell) : List (Fin requests.size) :=
  (List.finRange requests.size).filter (fun i =>
    decide (PrefixRequestKey.prefixPart requests[i.val]=digits ∧ PrefixRequestKey.pairPart requests[i.val]=pair))

theorem run_bucket (requests : Array (Vector (Fin 4) (P+ell)))
    (digits : Vector (Fin 4) P) (pair : Key ell) :
    BooleanRequestRouter.bucket (run requests).value (code digits pair)=selected requests digits pair := by
  simp only [run,BooleanRequestRouter.build_bucket,BooleanRequestRouter.selected,rows,selected]
  rw [List.ofFn_eq_map]
  simp only [List.filterMap_map,Function.comp_apply]
  have hh (i : Fin requests.size) :
      (if (address requests[i.val]).value=code digits pair then some i else none)=
      if decide (PrefixRequestKey.prefixPart requests[i.val]=digits ∧ PrefixRequestKey.pairPart requests[i.val]=pair)
        then some i else none := by
    simp only [address_eq_iff,decide_eq_true_eq]
  simp only [hh]
  exact congrFun List.filterMap_eq_filter (List.finRange requests.size)

theorem mem_bucket (requests : Array (Vector (Fin 4) (P+ell)))
    (digits : Vector (Fin 4) P) (pair : Key ell) (i : Fin requests.size) :
    i∈BooleanRequestRouter.bucket (run requests).value (code digits pair) ↔
      PrefixRequestKey.prefixPart requests[i.val]=digits ∧ PrefixRequestKey.pairPart requests[i.val]=pair := by
  rw [run_bucket]
  simp [selected]

theorem own_bucket (requests : Array (Vector (Fin 4) (P+ell))) (i : Fin requests.size) :
    i∈BooleanRequestRouter.bucket (run requests).value (address requests[i.val]).value := by
  exact (mem_bucket requests _ _ i).mpr ⟨rfl,rfl⟩

theorem unique_bucket (requests : Array (Vector (Fin 4) (P+ell))) (i : Fin requests.size)
    (digits other : Vector (Fin 4) P) (pair otherPair : Key ell)
    (h : i∈BooleanRequestRouter.bucket (run requests).value (code digits pair))
    (h' : i∈BooleanRequestRouter.bucket (run requests).value (code other otherPair)) :
    digits=other ∧ pair=otherPair := by
  have h1 := (mem_bucket requests digits pair i).mp h
  have h2 := (mem_bucket requests other otherPair i).mp h'
  exact ⟨h1.1.symm.trans h2.1,h1.2.symm.trans h2.2⟩

theorem bucket_nodup (requests : Array (Vector (Fin 4) (P+ell)))
    (digits : Vector (Fin 4) P) (pair : Key ell) :
    (BooleanRequestRouter.bucket (run requests).value (code digits pair)).Nodup := by
  rw [run_bucket]
  exact (List.nodup_finRange _).filter _

theorem run_items (requests : Array (Vector (Fin 4) (P+ell))) :
    BooleanRequestRouter.items (run requests).value=requests.size := by
  simp only [run,BooleanRequestRouter.build_items,rows,List.length_ofFn]

theorem run_cost (requests : Array (Vector (Fin 4) (P+ell))) :
    (run requests).bitSteps=0 ∧
    (run requests).control≤12*2^(P+(P+ell))+
      requests.size*(16*(P+(P+ell)+1)^2+64*(P+ell+1)+36)+20 := by
  have hh := BooleanRequestRouter.build_cost (rows requests)
  simp only [rows,List.length_ofFn] at hh
  refine ⟨hh.1,?_⟩
  simp only [run,rows]
  nlinarith [hh.2]

#print axioms code_get
#print axioms digit_injective
#print axioms code_eq_iff
#print axioms address_eq_iff
#print axioms run_bucket
#print axioms mem_bucket
#print axioms own_bucket
#print axioms unique_bucket
#print axioms bucket_nodup
#print axioms run_items
#print axioms run_cost
end ThinMatrix.PrefixRequestRouting
