import FiniteRequestRouter
import GraphOwnResiduals

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Route physical graph requests to their own band and two good masks
before residual projection/completion. Occurrence IDs are preserved; a
root gathers only its routed rows. Every degree/channel/window may reuse
the retained routing, without evaluating all requests at every mask pair. -/
namespace ThinMatrix.GraphOwnBandRouter
open scoped BigOperators
open GoodMapEmbedding BinaryGroupedCoordinates
variable {S L m C M : ℕ}

def count (S L m : ℕ) : ℕ := S*((goodSlots L m).card*(goodSlots L m).card)

def encode (a : Fin S) (normal opposite : Fin (goodSlots L m).card) : Fin (count S L m) :=
  finProdFinEquiv (a,finProdFinEquiv (normal,opposite))

def ownBand (right : Bool) (q : GraphCompletionRequests.Physical L m C) : ℕ :=
  if right then q.bandR else q.bandL

def accepts (a : ℕ) (right : Bool) (normal opposite : Fin (goodSlots L m).card)
    (q : GraphCompletionRequests.Physical L m C) : Bool :=
  decide (ownBand right q=a ∧ (RootRequestSelection.ranks right q).1=normal ∧
    (RootRequestSelection.ranks right q).2=opposite)

def key (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (hL : q.bandL<S) (hR : q.bandR<S) : Fin (count S L m) :=
  encode ⟨ownBand right q,by cases right <;> assumption⟩
    (RootRequestSelection.ranks right q).1 (RootRequestSelection.ranks right q).2

theorem key_eq_iff (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (hL : q.bandL<S) (hR : q.bandR<S) (a : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    key right q hL hR=encode a normal opposite ↔ accepts a.val right normal opposite q=true := by
  simp only [accepts,decide_eq_true_eq]
  constructor
  · intro h
    have hh := Prod.mk.inj (finProdFinEquiv.injective h)
    have hm := Prod.mk.inj (finProdFinEquiv.injective hh.2)
    exact ⟨congrArg Fin.val hh.1,hm.1,hm.2⟩
  · rintro ⟨ha,hn,ho⟩
    have hown : (⟨ownBand right q,by cases right <;> assumption⟩ : Fin S)=a := Fin.ext ha
    unfold key encode
    rw [hown,hn,ho]

theorem accepts_old (a : ℕ) (right : Bool) (normal opposite : Fin (goodSlots L m).card)
    (q : GraphCompletionRequests.Physical L m C) (ha : accepts a right normal opposite q=true) :
    RootRequestSelection.accepts (if right then q.bandL else a) (if right then a else q.bandR)
      right normal opposite q=true := by
  rw [RootRequestSelection.matches_iff]
  simp only [accepts,decide_eq_true_eq] at ha
  cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true,ownBand] at ha ⊢ <;>
    exact ⟨by tauto,by tauto,ha.2.1,ha.2.2⟩

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
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card) : Run (List (Fin M)) :=
  FiniteRequestRouter.ids tree (encode a normal opposite)

theorem ids_mem (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i, (requests.get i).bandL<S ∧ (requests.get i).bandR<S)
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card) (i : Fin M) :
    i∈(ids (run right requests hb).value a normal opposite).value ↔
      accepts a.val right normal opposite (requests.get i)=true := by
  simp only [ids,run,FiniteRequestRouter.ids_value,FiniteRequestRouter.selected,List.mem_filter,
    List.mem_finRange,true_and,decide_eq_true_eq,keys,Vector.get_ofFn]
  exact key_eq_iff _ _ _ _ _ _ _

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
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card) (i : Fin M)
    (hi : i∈(ids (run right requests hb).value a normal opposite).value) :
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get normal).bits.get=
      (RowIndexing.rowUnrank store (if right then (requests.get i).column else (requests.get i).row)).1.val ∧
    SourceFormation.cubeSupport ((ResidualFamilyKeys.prepare store t).value.masks.get opposite).bits.get=
      (RowIndexing.rowUnrank store (if right then (requests.get i).row else (requests.get i).column)).1.val :=
  RootRequestSelection.selected_masks store t _ _ right normal opposite (requests.get i)
    (accepts_old a.val right normal opposite _ ((ids_mem right requests hb a normal opposite i).mp hi))

def decode (g : Fin (count S L m)) : Fin S × (Fin (goodSlots L m).card × Fin (goodSlots L m).card) :=
  let ab := finProdFinEquiv.symm g
  (ab.1,finProdFinEquiv.symm ab.2)

 theorem encode_decode (g : Fin (count S L m)) : encode (decode g).1 (decode g).2.1 (decode g).2.2=g := by
  simp only [decode,encode,Prod.mk.eta,Equiv.apply_symm_apply]

 theorem group_total (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    (∑ g : Fin (count S L m),(ids (run right requests hb).value (decode g).1 (decode g).2.1 (decode g).2.2).value.length)=M := by
  simp only [ids,run,encode_decode,FiniteRequestRouter.ids_value]
  exact FiniteRequestRouter.group_total _

def project (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) : Run (GraphOwnResiduals.Projected L m M) :=
  let ids := GraphOwnBandRouter.ids tree a normal opposite
  let gathered := FiniteRequestRouter.gather requests ids.value
  let values : Vector _ ids.value.length := ⟨gathered.value,by simp [gathered]⟩
  let out := GraphCompletionRequests.project right maskN maskO values
  ⟨⟨ids.value,out.value,by simp [out]⟩,ids.bitSteps+gathered.bitSteps+out.bitSteps,
    ids.control+gathered.control+out.control+12⟩

theorem project_get (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m)
    (j : Fin (GraphOwnBandRouter.ids tree a normal opposite).value.length) :
    (project right requests tree a normal opposite maskN maskO).value.residuals.labels[j.val]'(by simp [project])=
      (GraphCompletionRequests.project right maskN maskO requests).value.labels[
        ((GraphOwnBandRouter.ids tree a normal opposite).value[j.val]).val]'(by simp) := by
  rw [GraphCompletionRequests.project_get]
  simp only [project,GraphCompletionRequests.project_get]
  simp [FiniteRequestRouter.gather,Vector.get_eq_getElem]

theorem project_bits (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :
    (project right requests tree a normal opposite maskN maskO).bitSteps=0 := by
  simp only [project,GraphOwnBandRouter.ids,FiniteRequestRouter.ids,BooleanRequestRouter.read_bits,
    FiniteRequestRouter.gather,GraphCompletionRequests.project_bits,zero_add]

theorem project_control (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :
    (project right requests tree a normal opposite maskN maskO).control≤
      16*((GraphOwnBandRouter.count S L m).size+1)^2+64*((GraphOwnBandRouter.count S L m).size+1)^3+
      48*L+(GraphOwnBandRouter.ids tree a normal opposite).value.length*(32*(L-m)+80)+52 := by
  have hi := (FiniteRequestRouter.ids_cost tree (GraphOwnBandRouter.encode a normal opposite)).2
  have hp := GraphCompletionRequests.project_control right maskN maskO
    (⟨(FiniteRequestRouter.gather requests (GraphOwnBandRouter.ids tree a normal opposite).value).value,
      by simp⟩ : Vector _ (GraphOwnBandRouter.ids tree a normal opposite).value.length)
  change (GraphOwnBandRouter.ids tree a normal opposite).control≤_ at hi
  simp only [FiniteRequestRouter.gather] at hp
  simp only [project,FiniteRequestRouter.gather]
  nlinarith

structure WindowRequests (k ell M : ℕ) where
  indices : List (Fin M)
  labels : Array (Vector (Fin 4) (WindowPrefixProgram.prefixLength k ell+WindowPrefixProgram.length k ell))
  size_eq : labels.size=indices.length

def transport (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (input : GraphOwnResiduals.Projected L m M) : GroupedPreparation.Counted (WindowRequests (L-m) ell M) :=
  let out := WindowCompletionRequests.requests ell layout input.residuals.labels
  ⟨⟨input.indices,out.value,by simp [out,input.size_eq]⟩,out.work+8⟩

theorem transport_get (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (right : Bool) (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (GoodMapEmbedding.goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m)
    (j : Fin (GraphOwnBandRouter.ids tree a normal opposite).value.length) :
    (transport ell layout (project right requests tree a normal opposite maskN maskO).value).value.labels[j.val]'(by simp [transport,project])=
      (WindowCompletionRequests.requests ell layout (GraphCompletionRequests.project right maskN maskO requests).value.labels).value[
        ((GraphOwnBandRouter.ids tree a normal opposite).value[j.val]).val]'(by simp) := by
  have hl := WindowCompletionRequests.requests_get ell layout
    (project right requests tree a normal opposite maskN maskO).value.residuals.labels j.val
    (by simp [project])
  have hr := WindowCompletionRequests.requests_get ell layout
    (GraphCompletionRequests.project right maskN maskO requests).value.labels
    ((GraphOwnBandRouter.ids tree a normal opposite).value[j.val]).val (by simp)
  have hh := congrArg (fun q => (WindowCompletionRequests.transport ell layout
    (WindowCompletionRequests.orient q).value).value)
    (project_get right requests tree a normal opposite maskN maskO j)
  exact hl.trans (hh.trans hr.symm)

theorem transport_work (ell : ℕ) (layout : RetainedWindowPermutation.Layout (2*(L-m)))
    (input : GraphOwnResiduals.Projected L m M) :
    (transport ell layout input).work ≤ input.indices.length*(48*(L-m)+56)+16 := by
  have hh := WindowCompletionRequests.requests_work ell layout input.residuals.labels
  rw [input.size_eq] at hh
  exact Nat.add_le_add_right hh 8

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

#print axioms accepts_old
#print axioms key_eq_iff
#print axioms ids_mem
#print axioms total
#print axioms cost
#print axioms original_masks
#print axioms encode_decode
#print axioms group_total
#print axioms project_get
#print axioms project_bits
#print axioms project_control
#print axioms transport_get
#print axioms transport_work
end ThinMatrix.GraphOwnBandRouter
