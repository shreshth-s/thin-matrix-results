import GraphLowDegreeFilter

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Reindex the actual retained mask layouts into full physical words.
Only outside normal p1 words are omitted; the later ordinary forms annihilate
those words. This is a finite identity, with no execution-cost claim. -/
namespace ThinMatrix.PhysicalWordReindex
open WalshEmbedding ResidualFamilyKeys DistinguishedResidualSupport RetainedShiftedFactor
open scoped BigOperators

abbrev Words (L : ℕ) := (Fin L → NormalLetter) × (Fin L → OppositeLetter)

def layout {L m : ℕ} (a : Mask L m) : Layout L m (L-m) :=
  ResidualRootBridge.transport (ResidualLayout.equivalence a.bits) (selected_size a) (remaining_size a)

def splitWord {k : ℕ} (w : CroppedGroupedSuffix.Word (2*k)) :
    (Fin k → Fin 3) × (Fin k → Fin 3) :=
  (fun i => w (Fin.cast (by omega : k+k=2*k) (Fin.castAdd k i)),
   fun i => w (Fin.cast (by omega : k+k=2*k) (Fin.natAdd k i)))

def joinWord {k : ℕ} (a b : Fin k → Fin 3) : CroppedGroupedSuffix.Word (2*k) :=
  fun i => Fin.append a b (Fin.cast (by omega : 2*k=k+k) i)

theorem split_join {k : ℕ} (a b : Fin k → Fin 3) : splitWord (joinWord a b)=(a,b) := by
  apply Prod.ext <;> funext i <;> simp only [splitWord,joinWord,Fin.cast_cast,Fin.cast_eq_self,Fin.append_left,Fin.append_right]

theorem join_split {k : ℕ} (w : CroppedGroupedSuffix.Word (2*k)) :
    joinWord (splitWord w).1 (splitWord w).2=w := by
  funext i
  have hi : i=Fin.cast (by omega : k+k=2*k) (Fin.cast (by omega : 2*k=k+k) i) := by simp
  rw [hi]
  generalize Fin.cast (by omega : 2*k=k+k) i=j
  refine Fin.addCases (fun z => ?_) (fun z => ?_) j <;> simp only [joinWord,splitWord,Fin.cast_cast,Fin.cast_eq_self,Fin.append_left,Fin.append_right]

theorem normalInput_eq {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) :
    normalInput a b x.1 x.2.1=assemble (layout a) x.2.1 (fun i => normalRemaining ((splitWord x.1).1 i)) := by
  funext i
  rcases he : ResidualLayout.equivalence a.bits i with j | j
  · simp [normalInput,assemble,layout,ResidualRootBridge.transport,he]
  · simp only [normalInput,assemble,layout,ResidualRootBridge.transport,Equiv.trans_apply,
      Equiv.sumCongr_apply,he,Sum.map_inr,Sum.elim_inr,finCongr_apply,splitWord]
    congr 2

theorem oppositeInput_eq {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) :
    oppositeInput a b x.1 x.2.2=assemble (layout b) x.2.2 (fun i => SourceCoordinates.oppositeEquiv ((splitWord x.1).2 i)) := by
  funext i
  rcases he : ResidualLayout.equivalence b.bits i with j | j
  · simp [oppositeInput,assemble,layout,ResidualRootBridge.transport,he]
  · simp only [oppositeInput,assemble,layout,ResidualRootBridge.transport,Equiv.trans_apply,
      Equiv.sumCongr_apply,he,Sum.map_inr,Sum.elim_inr,finCongr_apply,splitWord]
    congr 2
    exact congrArg x.1 (Fin.ext (congrArg (fun z => z+j.val) (remaining_size a)))

def pack {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) : Words L :=
  (normalInput a b x.1 x.2.1,oppositeInput a b x.1 x.2.2)

def normalIndex : NormalLetter → Fin 3
  | .x1 | .p1 => 0
  | .x2 => 1
  | .p2 => 2

theorem index_normal (i : Fin 3) : normalIndex (normalRemaining i)=i := by fin_cases i <;> rfl

theorem normal_index (n : NormalLetter) (h : n≠.p1) : normalRemaining (normalIndex n)=n := by
  cases n <;> first | rfl | contradiction

def unpack {L m : ℕ} (a b : Mask L m) (w : Words L) : Data m (L-m) :=
  (joinWord (fun i => normalIndex (w.1 ((layout a).symm (Sum.inr i))))
    (fun i => SourceCoordinates.oppositeEquiv.symm (w.2 ((layout b).symm (Sum.inr i)))),
   (fun i => w.1 ((layout a).symm (Sum.inl i))),
   (fun i => w.2 ((layout b).symm (Sum.inl i))))

def Supported {L m : ℕ} (a : Mask L m) (w : Words L) : Prop :=
  ∀ i : Fin (L-m), w.1 ((layout a).symm (Sum.inr i))≠.p1

theorem pack_supported {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) : Supported a (pack a b x) := by
  intro i
  simp only [pack,normalInput_eq,assemble,Equiv.apply_symm_apply,Sum.elim_inr]
  generalize (splitWord x.1).1 i=z
  fin_cases z <;> decide

theorem unpack_pack {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) : unpack a b (pack a b x)=x := by
  simp only [unpack,pack,normalInput_eq,oppositeInput_eq,assemble,Equiv.apply_symm_apply,
    Sum.elim_inr,Sum.elim_inl,index_normal,Equiv.symm_apply_apply,join_split]

theorem pack_unpack {L m : ℕ} (a b : Mask L m) (w : Words L) (h : Supported a w) :
    pack a b (unpack a b w)=w := by
  apply Prod.ext
  · change normalInput a b _ _=w.1
    rw [normalInput_eq]
    funext i
    rcases he : layout a i with j | j
    · simp only [assemble,he,Sum.elim_inl,unpack]
      rw [← he,Equiv.symm_apply_apply]
    · simp only [assemble,he,Sum.elim_inr,unpack,split_join]
      rw [normal_index _ (h j),← he,Equiv.symm_apply_apply]
  · change oppositeInput a b _ _=w.2
    rw [oppositeInput_eq]
    funext i
    rcases he : layout b i with j | j
    · simp only [assemble,he,Sum.elim_inl,unpack]
      rw [← he,Equiv.symm_apply_apply]
    · simp only [assemble,he,Sum.elim_inr,unpack,split_join,Equiv.apply_symm_apply]
      rw [← he,Equiv.symm_apply_apply]

theorem pack_injective {L m : ℕ} (a b : Mask L m) : Function.Injective (pack a b) :=
  Function.LeftInverse.injective (unpack_pack a b)

theorem sum_physical {L m : ℕ} {R : Type*} [AddCommMonoid R]
    (a b : Mask L m) (F : Words L → R) (hz : ∀ w, ¬Supported a w → F w=0) :
    (∑ x : Data m (L-m), F (pack a b x))=∑ n, ∑ o, F (n,o) := by
  classical
  calc
    _ = ∑ w∈Finset.univ.filter (Supported a), F w := by
      refine Finset.sum_bij (fun x _ => pack a b x) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,pack_supported a b x⟩
      · intro x _ y _ he
        exact pack_injective a b he
      · intro w hw
        exact ⟨unpack a b w,Finset.mem_univ _,pack_unpack a b w (Finset.mem_filter.mp hw).2⟩
      · intro x _; rfl
    _ = ∑ w, F w := Finset.sum_subset (Finset.filter_subset _ _) (by
      intro w _ hn
      exact hz w (by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hn))
    _ = _ := Fintype.sum_prod_type F

def selectedPosition {L m : ℕ} (a : Mask L m) (i : Fin m) : Fin L := (layout a).symm (Sum.inl i)
def remainingPosition {L m : ℕ} (a : Mask L m) (i : Fin (L-m)) : Fin L := (layout a).symm (Sum.inr i)

theorem remaining_position {L m : ℕ} (a : Mask L m) (i : Fin (L-m)) :
    remainingPosition a i=(GraphCompletionRequests.positions a).value.get i := rfl

theorem pack_normal_selected {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) (i : Fin m) :
    (pack a b x).1 (selectedPosition a i)=x.2.1 i := by
  simp only [pack,normalInput_eq,selectedPosition,assemble,Equiv.apply_symm_apply,Sum.elim_inl]

theorem pack_opposite_selected {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) (i : Fin m) :
    (pack a b x).2 (selectedPosition b i)=x.2.2 i := by
  simp only [pack,oppositeInput_eq,selectedPosition,assemble,Equiv.apply_symm_apply,Sum.elim_inl]

theorem pack_normal_remaining {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) (i : Fin (L-m)) :
    (pack a b x).1 (remainingPosition a i)=normalRemaining ((splitWord x.1).1 i) := by
  simp only [pack,normalInput_eq,remainingPosition,assemble,Equiv.apply_symm_apply,Sum.elim_inr]

theorem pack_opposite_remaining {L m : ℕ} (a b : Mask L m) (x : Data m (L-m)) (i : Fin (L-m)) :
    (pack a b x).2 (remainingPosition b i)=SourceCoordinates.oppositeEquiv ((splitWord x.1).2 i) := by
  simp only [pack,oppositeInput_eq,remainingPosition,assemble,Equiv.apply_symm_apply,Sum.elim_inr]

#print axioms remaining_position
#print axioms pack_normal_selected
#print axioms pack_opposite_selected
#print axioms pack_normal_remaining
#print axioms pack_opposite_remaining
#print axioms sum_physical
#print axioms split_join
#print axioms join_split
#print axioms normalInput_eq
#print axioms oppositeInput_eq
#print axioms index_normal
#print axioms normal_index
#print axioms pack_supported
#print axioms unpack_pack
#print axioms pack_unpack
#print axioms pack_injective
end ThinMatrix.PhysicalWordReindex
