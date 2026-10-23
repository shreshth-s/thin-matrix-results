import BinaryBackendExecution
import ExactHalfCroppedEmbedding
import BinaryResidualDegreeSpace

set_option autoImplicit false

/-! Executable inverse weights from retained supported-subset candidates.
No inverse linear map or choice occurs in the program. Candidates, their
images and their binary-computed weights are stored once. Table scans use
Boolean/indexed control; their lowering to binary addresses is separate. -/
namespace ThinMatrix.ExactHalfWeightTable
open WalshEmbedding SourceFormation GoodMapEmbedding GoodSetConstruction
open BinaryGroupedCoordinates BinaryCroppedHighInput

theorem ofFn_get {n : ℕ} (b : Cube n) : (Vector.ofFn b).get=b := by
  funext i; simp

structure Candidate (L m : ℕ) where
  bits : Vector Bool L
  image : Vector Bool m
  weight : ℕ

def candidate {L m : ℕ} (columns : Vector (Vector Bool m) L) (bits : Vector Bool L) :
    Run (Candidate L m) :=
  let count := countBits bits.toList
  let decoded := BinaryModularCell.decodeUnsigned count.value
  ⟨⟨bits,Vector.ofFn (columnMap (columnFunction columns) bits.get),decoded.value⟩,
    count.bitSteps+decoded.bitSteps,100*(L+m+1)^3⟩

theorem candidate_weight {L m : ℕ} (columns : Vector (Vector Bool m) L) (bits : Vector Bool L) :
    (candidate columns bits).value.weight=ones bits.get := by
  simp [candidate,BinaryModularCell.decodeUnsigned_value,countBits_view,
    BinaryResidualDegreeSpace.toList_get,bitCount_ofFn]

def candidates {L m : ℕ} (columns : Vector (Vector Bool m) L) : Run (List (Candidate L m)) :=
  let entries := List.ofFn fun i : Fin (2^L) =>
    candidate columns (Vector.ofFn ((HalfSourceIntegerGreedy.cubeIndex L).symm i))
  ⟨entries.map (fun e => e.value),(entries.map (fun e => e.bitSteps)).sum,
    (entries.map (fun e => e.control)).sum+(4*L+12)*2^L+1⟩

theorem candidate_mem {L m : ℕ} (columns : Vector (Vector Bool m) L) (bits : Cube L) :
    (candidate columns (Vector.ofFn bits)).value ∈ (candidates columns).value := by
  apply List.mem_map.mpr
  refine ⟨candidate columns (Vector.ofFn bits),?_,rfl⟩
  apply List.mem_ofFn.mpr
  exact ⟨(HalfSourceIntegerGreedy.cubeIndex L) bits,by simp⟩

theorem candidates_spec {L m : ℕ} (columns : Vector (Vector Bool m) L)
    (c : Candidate L m) (hc : c ∈ (candidates columns).value) :
    c.image.get=columnMap (columnFunction columns) c.bits.get ∧ c.weight=ones c.bits.get := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  constructor
  · funext j; simp [candidate]
  · exact candidate_weight _ _

def accepts {L m : ℕ} (Q : Cube L) (h : Cube m) (c : Candidate L m) : Bool :=
  (List.finRange L).all (fun i => !c.bits.get i || Q i) && maskEqual c.image.get h

theorem accepts_true {L m : ℕ} (Q : Cube L) (h : Cube m) (c : Candidate L m) :
    accepts Q h c=true ↔ (∀ i, c.bits.get i=true → Q i=true) ∧ c.image.get=h := by
  simp only [accepts,Bool.and_eq_true,List.all_eq_true,List.mem_finRange,forall_true_left,
    Bool.or_eq_true,maskEqual_true]
  constructor
  · rintro ⟨ha,hb⟩; refine ⟨?_,hb⟩; intro i hi; rcases ha i with h | h
    · rw [hi] at h; contradiction
    · exact h
  · rintro ⟨ha,hb⟩; refine ⟨?_,hb⟩; intro i
    cases hi : c.bits.get i
    · exact Or.inl rfl
    · exact Or.inr (ha i hi)

def scan {L m : ℕ} (Q : Cube L) (h : Cube m) : List (Candidate L m) → Program ℕ
  | [] => ⟨0,1⟩
  | c::cs =>
      if accepts Q h c then ⟨c.weight,8*(L+m+1)⟩
      else let rest := scan Q h cs; ⟨rest.value,rest.operations+8*(L+m+1)⟩

theorem scan_correct {L m W : ℕ} (Q : Cube L) (h : Cube m) (cs : List (Candidate L m))
    (hs : ∀ c ∈ cs, accepts Q h c=true → c.weight=W)
    (he : ∃ c ∈ cs, accepts Q h c=true) : (scan Q h cs).value=W := by
  induction cs with
  | nil => simp at he
  | cons c cs ih =>
    by_cases hc : accepts Q h c=true
    · simpa [scan,hc] using hs c (by simp) hc
    · simp only [scan,hc]
      apply ih (fun d hd => hs d (by simp [hd]))
      obtain ⟨d,hd,ht⟩ := he
      rcases List.mem_cons.mp hd with h | h
      · subst d; exact False.elim (hc ht)
      · exact ⟨d,h,ht⟩

theorem scan_cost {L m : ℕ} (Q : Cube L) (h : Cube m) (cs : List (Candidate L m)) :
    (scan Q h cs).operations ≤ cs.length*(8*(L+m+1))+1 := by
  induction cs with
  | nil => simp [scan]
  | cons c cs ih => simp only [scan]; split <;> simp only [List.length_cons] <;> nlinarith

theorem scan_weight {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (Q : Finset (Fin L)) (hQ : Q ∈ goodSlots L m) (h : Cube m) :
    (scan (setBits Q) h (candidates shape.environment.gammaColumns).value).value =
      ExactHalfCroppedEmbedding.weight L m Q h := by
  let E := restrictedEquiv (constructGoodMaps L m).1 Q (goodSlots_size L m Q hQ)
    ((mem_goodSlots L m Q).mp hQ).2.1
  have hmap : ∀ T : Subsets Q,
      shape.environment.gamma (setBits T.val)=E T := by
    intro T; rw [shape.gamma]; exact restrictedEquiv_spec _ _ _ _ T
  apply scan_correct
  · intro c hc ha
    obtain ⟨hs,hi⟩ := (accepts_true _ _ _).mp ha
    obtain ⟨hcmap,hw⟩ := candidates_spec _ c hc
    let T : Subsets Q := ⟨cubeSupport c.bits.get,by
      intro i hi; have hb : c.bits.get i=true := by simpa [cubeSupport] using hi
      simpa [setBits] using hs i hb⟩
    have hb : setBits T.val=c.bits.get := by funext i; simp [T,setBits,cubeSupport]
    have he : E T=h := by rw [← hmap T,hb]; exact hcmap.symm.trans hi
    have ht : T=E.symm h := by rw [← he]; exact (E.symm_apply_apply T).symm
    rw [hw,← hb,ones_setBits,ht]
    simp only [ExactHalfCroppedEmbedding.weight,dif_pos hQ,ExactHalfGoodMap.inverseWeight]
    rfl
  · let c := (candidate shape.environment.gammaColumns (Vector.ofFn (setBits (E.symm h).val))).value
    refine ⟨c,candidate_mem _ _,(accepts_true _ _ _).mpr ⟨?_,?_⟩⟩
    · intro i hi
      have hm : i ∈ (E.symm h).val := by simpa [c,candidate,setBits] using hi
      simp [setBits,(E.symm h).property hm]
    · have hs := hmap (E.symm h)
      rw [E.apply_symm_apply] at hs
      simpa only [c,candidate,ofFn_get,Environment.gamma] using hs

abbrev Store (L m : ℕ) := Table (Table ℕ 2 m) 2 L

def build {L m : ℕ} (good : GoodStore L) (cs : List (Candidate L m)) : Program (Store L m) :=
  tableBuild 2 L fun Q => tableBuild 2 m fun h =>
    let allowed := tableReadProgram 2 L good Q
    if allowed.value then
      let found := scan (keyCube Q) (keyCube h) cs
      ⟨found.value,allowed.operations+found.operations+4⟩
    else ⟨0,allowed.operations+4⟩

def read {L m : ℕ} (store : Store L m) (Q : Finset (Fin L)) (h : Cube m) : ℕ :=
  tableRead 2 m (tableRead 2 L store (cubeKey (setBits Q))) (cubeKey h)

theorem read_build {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m)
    (Q : Finset (Fin L)) (h : Cube m) :
    read (build shape.environment.good (candidates shape.environment.gammaColumns).value).value Q h =
      ExactHalfCroppedEmbedding.weight L m Q h := by
  simp only [read,build,tableRead_build,tableReadProgram_value,keyCube_cubeKey]
  have hg := shape.good Q
  change tableRead 2 L shape.environment.good (cubeKey (setBits Q)) = _ at hg
  rw [hg]
  by_cases hQ : Q ∈ goodSlots L m
  · simp only [hQ,decide_true,↓reduceIte]; exact scan_weight shape Q hQ h
  · simp [hQ,ExactHalfCroppedEmbedding.weight]

def candidateBitBudget (L : ℕ) : ℕ :=
  L*(BackendScalarBits.backendScalarUnit (L.size+1)+4)+1+8*(L.size+1)^2

theorem candidate_bits {L m : ℕ} (columns : Vector (Vector Bool m) L) (bits : Vector Bool L) :
    (candidate columns bits).bitSteps ≤ candidateBitBudget L := by
  have hc := countBits_price bits.toList L (by simp)
  have hd := BinaryModularCell.decodeUnsigned_price L.size (countBits bits.toList).value (by
    rw [countBits_view,Int.natAbs_natCast]
    exact Nat.size_le_size (by simpa using bitCount_le bits.toList))
  simp only [Vector.length_toList] at hc
  exact Nat.add_le_add hc hd

theorem candidates_bits {L m : ℕ} (columns : Vector (Vector Bool m) L) :
    (candidates columns).bitSteps ≤ 2^L*candidateBitBudget L := by
  unfold candidates
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ ≤ ∑ _i : Fin (2^L), candidateBitBudget L := Finset.sum_le_sum (fun i _ => candidate_bits _ _)
    _ = _ := by simp

theorem candidates_control {L m : ℕ} (columns : Vector (Vector Bool m) L) :
    (candidates columns).control=(100*(L+m+1)^3+4*L+12)*2^L+1 := by
  simp only [candidates,List.map_ofFn,List.sum_ofFn,Function.comp_apply,candidate]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def buildBudget (L m : ℕ) : ℕ :=
  ((2*L+6+2^L*(8*(L+m+1))+16*m)*2^m+16*L)*2^L

theorem build_cost {L m : ℕ} (shape : ThinMatrixBackend.ShapePlan L m) :
    (build shape.environment.good (candidates shape.environment.gammaColumns).value).operations ≤ buildBudget L m := by
  apply tableBuild_cost
  intro Q
  apply tableBuild_cost
  intro h
  have hs := scan_cost (keyCube Q) (keyCube h) (candidates shape.environment.gammaColumns).value
  have hn : (candidates shape.environment.gammaColumns).value.length=2^L := by simp [candidates]
  rw [hn] at hs
  simp only [tableReadProgram_cost]
  split <;> dsimp only <;> omega

#print axioms ofFn_get
#print axioms candidate_weight
#print axioms candidate_mem
#print axioms candidates_spec
#print axioms accepts_true
#print axioms scan_correct
#print axioms scan_cost
#print axioms scan_weight
#print axioms read_build
#print axioms candidate_bits
#print axioms candidates_bits
#print axioms candidates_control
#print axioms build_cost
end ThinMatrix.ExactHalfWeightTable
