import FiniteRequestRouter
import FoldedRequestBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Route physical graph requests to their own band and two good masks
before residual projection/completion. Occurrence IDs are preserved; a
root gathers only its routed rows. Every degree/channel/window may reuse
the retained routing, without evaluating all requests at every mask pair. -/
namespace ThinMatrix.GraphOwnRequestRouter
open scoped BigOperators
open GoodMapEmbedding BinaryGroupedCoordinates
variable {S L m C M : ℕ}

def count (S L m : ℕ) : ℕ := (S*(goodSlots L m).card)*(S*(goodSlots L m).card)

def encode (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) : Fin (count S L m) :=
  finProdFinEquiv (finProdFinEquiv (a,normal),finProdFinEquiv (b,opposite))

def key (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (hL : q.bandL<S) (hR : q.bandR<S) : Fin (count S L m) :=
  encode ⟨q.bandL,hL⟩ ⟨q.bandR,hR⟩ (RootRequestSelection.ranks right q).1 (RootRequestSelection.ranks right q).2

theorem key_eq_iff (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (hL : q.bandL<S) (hR : q.bandR<S) (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    key right q hL hR=encode a b normal opposite ↔
      RootRequestSelection.accepts a.val b.val right normal opposite q=true := by
  rw [RootRequestSelection.matches_iff]
  constructor
  · intro h
    have hh := Prod.mk.inj (finProdFinEquiv.injective h)
    have hl := Prod.mk.inj (finProdFinEquiv.injective hh.1)
    have hr := Prod.mk.inj (finProdFinEquiv.injective hh.2)
    exact ⟨congrArg Fin.val hl.1,congrArg Fin.val hr.1,hl.2,hr.2⟩
  · rintro ⟨hl,hr,hn,ho⟩
    have hla : (⟨q.bandL,hL⟩ : Fin S)=a := Fin.ext hl
    have hra : (⟨q.bandR,hR⟩ : Fin S)=b := Fin.ext hr
    unfold key encode
    rw [hla,hra,hn,ho]

def keys (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    Run (Vector (Fin (count S L m)) M) :=
  ⟨Vector.ofFn (fun i => key right (requests.get i) (hb i).1 (hb i).2),0,
    M*(128*((count S L m).size+L+m+1)^3)+8⟩

def run (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    Run (BooleanRequestRouter.Tree (Fin M) (count S L m).size) :=
  let tagged := keys right requests hb
  let out := FiniteRequestRouter.run tagged.value
  ⟨out.value,tagged.bitSteps+out.bitSteps,tagged.control+out.control+8⟩

def ids (tree : BooleanRequestRouter.Tree (Fin M) (count S L m).size)
    (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) : Run (List (Fin M)) :=
  FiniteRequestRouter.ids tree (encode a b normal opposite)

theorem ids_mem (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) (i : Fin M) :
    i∈(ids (run right requests hb).value a b normal opposite).value ↔
      RootRequestSelection.accepts a.val b.val right normal opposite (requests.get i)=true := by
  simp only [ids,run,FiniteRequestRouter.ids_value,FiniteRequestRouter.selected,List.mem_filter,
    List.mem_finRange,true_and,decide_eq_true_eq,keys,Vector.get_ofFn]
  exact key_eq_iff _ _ _ _ _ _ _ _

theorem total (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    BooleanRequestRouter.items (run right requests hb).value=M := FiniteRequestRouter.total _

theorem cost (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (run right requests hb).bitSteps=0 ∧ (run right requests hb).control≤
      24*(count S L m+1)+M*(16*((count S L m).size+1)^2+64*((count S L m).size+1)^3+
        128*((count S L m).size+L+m+1)^3+36)+36 := by
  have hh := FiniteRequestRouter.cost (keys right requests hb).value
  refine ⟨by simpa only [run,keys,zero_add] using hh.1,?_⟩
  simp only [keys] at hh
  simp only [run,keys]
  nlinarith [hh.2]

theorem original_masks (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (store : RowIndexing.GoodIndexStore L m) (t : ℕ)
    (a b : Fin S) (normal opposite : Fin (goodSlots L m).card) (i : Fin M)
    (hi : i∈(ids (run right requests hb).value a b normal opposite).value) :
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get normal).bits.get=
      (RowIndexing.rowUnrank store (if right then (requests.get i).column else (requests.get i).row)).1.val ∧
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get opposite).bits.get=
      (RowIndexing.rowUnrank store (if right then (requests.get i).row else (requests.get i).column)).1.val :=
  RootRequestSelection.selected_masks store t a.val b.val right normal opposite (requests.get i)
    ((ids_mem right requests hb a b normal opposite i).mp hi)

/-- The actual graph source supplies bounded physical tags; no assumed tag
range or independently chosen mask is needed by the executable routing. -/
def fromTarget {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (right : Bool)
    (target : BinaryFoldedFormation.BinaryTable n) :=
  let shape := BinaryBackendExecution.prepareShapeRuntime p.L p.m
  let physical := GraphCompletionRequests.prepare f p shape target
  have hb (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
      (physical.physical.value.get i).bandL<TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m) ∧
      (physical.physical.value.get i).bandR<TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth p.L p.m) := by
    simpa only [physical,GraphCompletionRequests.prepare_get,shape,FoldedBandTransport.physical,
      FoldedBandTransport.request] using FoldedRequestBounds.bands_lt f p target i
  let routed := run right physical.physical.value hb
  (physical,routed)

#print axioms key_eq_iff
#print axioms ids_mem
#print axioms total
#print axioms cost
#print axioms original_masks
end ThinMatrix.GraphOwnRequestRouter
