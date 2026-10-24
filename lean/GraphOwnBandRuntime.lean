import GraphOwnBandRouter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Retain the actual mask cardinality once. Runtime index arithmetic uses
that stored size, and never regenerates the selected good-mask family. -/
namespace ThinMatrix.GraphOwnBandRuntime
open GoodMapEmbedding BinaryGroupedCoordinates
variable {S L m C M : ℕ}

structure Shape (L m : ℕ) where
  masks : ℕ
  correct : masks=(goodSlots L m).card

def prepare (masks : Vector (ResidualFamilyKeys.Mask L m) (goodSlots L m).card) : Shape L m :=
  ⟨masks.toArray.size,masks.size_toArray⟩

def groups (shape : Shape L m) (S : ℕ) : ℕ := S*(shape.masks*shape.masks)

 theorem groups_eq (shape : Shape L m) : groups shape S=GraphOwnBandRouter.count S L m := by
  simp only [groups,shape.correct,GraphOwnBandRouter.count]

def encode (shape : Shape L m) (a : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    Fin (groups shape S) :=
  finProdFinEquiv (a,finProdFinEquiv (Fin.cast shape.correct.symm normal,Fin.cast shape.correct.symm opposite))

 theorem encode_eq (shape : Shape L m) (a : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    Fin.cast (groups_eq shape) (encode shape a normal opposite)=GraphOwnBandRouter.encode a normal opposite := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

def decode (shape : Shape L m) (g : Fin (GraphOwnBandRouter.count S L m)) :
    Fin S × (Fin (goodSlots L m).card × Fin (goodSlots L m).card) :=
  let ab := finProdFinEquiv.symm (Fin.cast (groups_eq shape).symm g)
  let no := finProdFinEquiv.symm ab.2
  (ab.1,Fin.cast shape.correct no.1,Fin.cast shape.correct no.2)

 theorem decode_eq (shape : Shape L m) (g : Fin (GraphOwnBandRouter.count S L m)) :
    decode shape g=GraphOwnBandRouter.decode g := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

def key (shape : Shape L m) (right : Bool) (q : GraphCompletionRequests.Physical L m C)
    (hL : q.bandL<S) (hR : q.bandR<S) : Fin (groups shape S) :=
  encode shape ⟨GraphOwnBandRouter.ownBand right q,by cases right <;> assumption⟩
    (RootRequestSelection.ranks right q).1 (RootRequestSelection.ranks right q).2

def run (shape : Shape L m) (right : Bool)
    (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    Run (BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size) :=
  let keys := Vector.ofFn fun i => key shape right (requests.get i) (hb i).1 (hb i).2
  let out := FiniteRequestRouter.run keys
  ⟨cast (congrArg (fun G => BooleanRequestRouter.Tree (Fin M) G.size) (groups_eq shape)) out.value,
    out.bitSteps,M*(128*((groups shape S).size+L+m+1)^3)+8+out.control+8⟩

 theorem run_eq (shape : Shape L m) (right : Bool)
    (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (hb : ∀ i,(requests.get i).bandL<S ∧ (requests.get i).bandR<S) :
    run shape right requests hb=GraphOwnBandRouter.run right requests hb := by
  rcases shape with ⟨K,hK⟩
  subst K
  simp only [run,GraphOwnBandRouter.run,GraphOwnBandRouter.keys,Nat.zero_add]
  rfl

def ids (shape : Shape L m)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card) : Run (List (Fin M)) :=
  let actual := cast (congrArg (fun G => BooleanRequestRouter.Tree (Fin M) G.size) (groups_eq shape).symm) tree
  FiniteRequestRouter.ids actual (encode shape a normal opposite)

 theorem ids_eq (shape : Shape L m)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card) :
    ids shape tree a normal opposite=GraphOwnBandRouter.ids tree a normal opposite := by
  rcases shape with ⟨K,hK⟩
  subst K
  rfl

def project (shape : Shape L m) (right : Bool)
    (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) : Run (GraphOwnResiduals.Projected L m M) :=
  let found := ids shape tree a normal opposite
  let gathered := FiniteRequestRouter.gather requests found.value
  let values : Vector _ found.value.length := ⟨gathered.value,by simp [gathered]⟩
  let out := GraphCompletionRequests.project right maskN maskO values
  ⟨⟨found.value,out.value,by simp [out]⟩,found.bitSteps+gathered.bitSteps+out.bitSteps,
    found.control+gathered.control+out.control+12⟩

 theorem project_eq (shape : Shape L m) (right : Bool)
    (requests : Vector (GraphCompletionRequests.Physical L m C) M)
    (tree : BooleanRequestRouter.Tree (Fin M) (GraphOwnBandRouter.count S L m).size)
    (a : Fin S) (normal opposite : Fin (goodSlots L m).card)
    (maskN maskO : ResidualFamilyKeys.Mask L m) :
    project shape right requests tree a normal opposite maskN maskO=
      GraphOwnBandRouter.project right requests tree a normal opposite maskN maskO := by
  simp only [project,ids_eq,GraphOwnBandRouter.project]
  rfl

#print axioms groups_eq
#print axioms encode_eq
#print axioms decode_eq
#print axioms run_eq
#print axioms ids_eq
#print axioms project_eq
end ThinMatrix.GraphOwnBandRuntime
