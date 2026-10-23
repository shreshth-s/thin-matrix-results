import ExactHalfGraphSources
import CompleteResidualArray

set_option autoImplicit false

/-! Retained good-mask and joint channel keys for LOW roots. Good masks are
read from the existing compact good-code store. The capped-prefix recursion
visits only admissible channel prefixes. Costs here are indexed control;
no binary address implementation is claimed. -/
namespace ThinMatrix.ResidualFamilyKeys
open WalshEmbedding GoodMapEmbedding SourceFormation BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators

structure Mask (L m : ℕ) where
  bits : Vector Bool L
  good : cubeSupport bits.get ∈ goodSlots L m

theorem selected_size {L m : ℕ} (a : Mask L m) : (ResidualLayout.selected a.bits).length=m := by
  have h := goodSlots_size L m _ a.good
  have he : (ResidualLayout.selected a.bits).toFinset=cubeSupport a.bits.get := by
    ext i; simp [ResidualLayout.mem_selected,cubeSupport]
  rw [← List.toFinset_card_of_nodup (ResidualLayout.selected_nodup a.bits),he,h]

theorem remaining_size {L m : ℕ} (a : Mask L m) : (ResidualLayout.remaining a.bits).length=L-m := by
  have h := ResidualLayout.lengths a.bits
  rw [selected_size] at h
  omega

/-- Repeated quotient/remainder by two, retaining every Boolean prefix.
The annotation charges the prefix copy and scalar/register steps explicitly. -/
def decode : (n : ℕ) → ℕ → Run (Vector Bool n)
  | 0,_ => ⟨Vector.replicate 0 false,0,4⟩
  | n+1,x =>
      let rest := decode n (x/2)
      ⟨CappedBitPreparation.prepend (x%2==1) rest.value,rest.bitSteps,rest.control+8*(n+1)+16⟩

theorem decode_get (n x : ℕ) (i : Fin n) : (decode n x).value.get i=(x/2^i.val%2==1) := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decode]
    · simp only [decode,CappedBitPreparation.prepend_succ,ih,Fin.val_succ]
      rw [Nat.div_div_eq_div_mul,pow_succ']

theorem decode_cube (n : ℕ) (i : Fin (2^n)) :
    (decode n i.val).value.get=(RowIndexing.cubeEquiv n).symm i := by
  funext j
  rw [decode_get]
  apply Bool.eq_iff_iff.mpr
  change (i.val/2^j.val%2==1)=true ↔ (finFunctionFinEquiv.symm i j == (1 : Fin 2))=true
  simp [Fin.ext_iff,finFunctionFinEquiv_symm_apply_val]

theorem decode_bits (n x : ℕ) : (decode n x).bitSteps=0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (x/2)

def decodeBudget (n : ℕ) : ℕ := 4*n^2+20*n+4

theorem decode_control (n x : ℕ) : (decode n x).control=decodeBudget n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [decode,ih,decodeBudget]; ring

def maskProgram {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : Run (Mask L m) :=
  let out := decode L (store.codes.get i).val
  ⟨⟨out.value,by
    simpa only [out,decode_cube,RowIndexing.goodUnrank] using (RowIndexing.goodUnrank store i).property⟩,
    out.bitSteps,out.control+8⟩

def maskAt {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : Mask L m := (maskProgram store i).value

theorem maskAt_support {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) :
    cubeSupport (maskAt store i).bits.get=((RowIndexing.goodRankEquiv L m).symm i).val := by
  simpa only [maskAt,maskProgram,decode_cube,RowIndexing.goodUnrank] using
    congrArg Subtype.val (RowIndexing.goodUnrank_value store i)

theorem maskAt_unique {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (i j : Fin (goodSlots L m).card) (h : (maskAt store i).bits=(maskAt store j).bits) : i=j := by
  have he := congrArg (fun b : Vector Bool L => cubeSupport b.get) h
  rw [maskAt_support,maskAt_support] at he
  exact (RowIndexing.goodRankEquiv L m).symm.injective (Subtype.ext he)

def masks {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) :
    Run (Vector (Mask L m) (goodSlots L m).card) :=
  tabulate store.codes (maskProgram store)

@[simp] theorem masks_get {L m : ℕ} (store : RowIndexing.GoodIndexStore L m)
    (i : Fin (goodSlots L m).card) : (masks store).value.get i=maskAt store i := by simp [masks,maskAt]

theorem masks_cover {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (Q : RowIndexing.GoodSlot L m) :
    ∃! i, cubeSupport ((masks store).value.get i).bits.get=Q.val := by
  refine ⟨RowIndexing.goodRankEquiv L m Q,?_,?_⟩
  · simp [maskAt_support]
  · intro i hi
    rw [masks_get,maskAt_support] at hi
    exact (RowIndexing.goodRankEquiv L m).symm.injective (by
      simpa using (Subtype.ext hi : (RowIndexing.goodRankEquiv L m).symm i=Q))

theorem masks_bits {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) : (masks store).bitSteps=0 := by
  simp [masks,tabulate_bits_eq,maskProgram,decode_bits]

theorem masks_control {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) :
    (masks store).control≤(goodSlots L m).card*(decodeBudget L+40)+8 := by
  apply tabulate_control
  intro i
  simp only [maskProgram,decode_control]
  omega

abbrev Channel (m : ℕ) := Vector Bool (m+m)
def normal {m : ℕ} (c : Channel m) : Vector Bool m := Vector.ofFn (fun i => c.get (Fin.castAdd m i))
def opposite {m : ℕ} (c : Channel m) : Vector Bool m := Vector.ofFn (fun i => c.get (Fin.natAdd m i))

theorem join_split {m : ℕ} (c : Channel m) : normal c ++ opposite c=c := by
  apply Vector.ext
  intro i hi
  change (normal c ++ opposite c).get ⟨i,hi⟩=c.get ⟨i,hi⟩
  exact Fin.addCases (by intro j; simp [normal,Vector.get]) (by intro j; simp [opposite,Vector.get]) ⟨i,hi⟩

theorem split_join {m : ℕ} (a b : Vector Bool m) : normal (a++b)=a ∧ opposite (a++b)=b := by
  constructor <;> ext i hi <;> simp [normal,opposite,Vector.get]

theorem ones_join {m : ℕ} (a b : Vector Bool m) :
    CappedBitPreparation.ones (a++b)=CappedBitPreparation.ones a+CappedBitPreparation.ones b := by
  simp [CappedBitPreparation.ones]

def channelCount (m t : ℕ) : ℕ := if t=0 then 0 else CappedSubsetList.count (m+m) (t-1)

theorem channelCount_sum (m t : ℕ) : channelCount m t=∑ h∈Finset.range t, (2*m).choose h := by
  by_cases ht : t=0
  · simp [channelCount,ht]
  · have hh : t-1+1=t := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ht)
    simp only [channelCount,if_neg ht,CappedSubsetList.count,hh,two_mul]

def channels (m t : ℕ) : Run (List (Channel m)) :=
  if t=0 then ⟨[],0,2⟩ else
    let out := CappedBitPreparation.execute (m+m) (t-1)
    ⟨out.keys,0,out.work+4⟩

theorem channels_mem (m t : ℕ) (c : Channel m) :
    c∈(channels m t).value ↔ CappedBitPreparation.ones c<t := by
  by_cases ht : t=0
  · simp [channels,ht]
  · simp only [channels,if_neg ht,CappedBitPreparation.execute_keys,CappedBitPreparation.mem_generate]
    omega

theorem channels_pairs (m t : ℕ) (a b : Vector Bool m) :
    a++b∈(channels m t).value ↔ CappedBitPreparation.ones a+CappedBitPreparation.ones b<t := by
  rw [channels_mem,ones_join]

theorem channels_nodup (m t : ℕ) : (channels m t).value.Nodup := by
  by_cases ht : t=0
  · simp [channels,ht]
  · simpa [channels,ht] using CappedBitPreparation.generate_nodup (m+m) (t-1)

theorem channels_length (m t : ℕ) : (channels m t).value.length=channelCount m t := by
  by_cases ht : t=0 <;> simp [channels,channelCount,ht,CappedBitPreparation.generate_length]

theorem channels_bits (m t : ℕ) : (channels m t).bitSteps=0 := by unfold channels; split <;> rfl

theorem channels_control (m t : ℕ) :
    (channels m t).control≤(2*m+1)*(16*m+32)*channelCount m t+4 := by
  by_cases ht : t=0
  · simp [channels,channelCount,ht]
  · have h := CappedBitPreparation.work_bound (m+m) (t-1)
    simp only [channels,channelCount,if_neg ht]
    nlinarith [h]

structure Prepared (L m t : ℕ) where
  masks : Vector (Mask L m) (goodSlots L m).card
  channels : Vector (Channel m) (channelCount m t)

def prepare {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ) : Run (Prepared L m t) :=
  let ms := masks store
  let cs := channels m t
  ⟨⟨ms.value,⟨cs.value.toArray,by simp [cs,channels_length]⟩⟩,
    ms.bitSteps+cs.bitSteps,ms.control+cs.control+2*cs.value.length+8⟩

theorem prepare_masks {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ)
    (i : Fin (goodSlots L m).card) : (prepare store t).value.masks.get i=maskAt store i := masks_get store i

theorem prepare_channels {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ) :
    (prepare store t).value.channels.toList=(channels m t).value := by simp [prepare]

def prepareBudget (L m t G : ℕ) : ℕ :=
  G*(decodeBudget L+40)+8+(2*m+1)*(16*m+32)*channelCount m t+4+2*channelCount m t+8

theorem prepare_bits {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ) :
    (prepare store t).bitSteps=0 := by simp [prepare,masks_bits,channels_bits]

theorem prepare_control {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ) :
    (prepare store t).control≤prepareBudget L m t (goodSlots L m).card := by
  have hm := masks_control store
  have hc := channels_control m t
  simp only [prepare,prepareBudget,channels_length]
  omega

theorem prepare_channel_injective {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ) :
    Function.Injective (prepare store t).value.channels.get := by
  intro i j h
  have hn : (prepare store t).value.channels.toList.Nodup := by
    rw [prepare_channels]; exact channels_nodup m t
  apply Fin.ext
  apply (hn.getElem_inj_iff (i := i.val) (j := j.val) (hi := by simp) (hj := by simp)).mp
  simpa [Vector.get] using h

theorem prepare_channel_cover {L m : ℕ} (store : RowIndexing.GoodIndexStore L m) (t : ℕ)
    (c : Channel m) (hc : CappedBitPreparation.ones c<t) :
    ∃! i, (prepare store t).value.channels.get i=c := by
  have hm : c∈(prepare store t).value.channels.toList := by
    rw [prepare_channels]; exact (channels_mem m t c).mpr hc
  obtain ⟨i,hi,he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hm)
  refine ⟨⟨i,hi⟩,he,?_⟩
  intro j hj
  exact prepare_channel_injective store t (hj.trans he.symm)

#print axioms prepare_channel_injective
#print axioms prepare_channel_cover
#print axioms prepare_masks
#print axioms prepare_channels
#print axioms prepare_bits
#print axioms prepare_control
#print axioms decode_get
#print axioms decode_cube
#print axioms decode_bits
#print axioms decode_control
#print axioms selected_size
#print axioms remaining_size
#print axioms maskAt_support
#print axioms maskAt_unique
#print axioms masks_get
#print axioms masks_cover
#print axioms masks_bits
#print axioms masks_control
#print axioms join_split
#print axioms split_join
#print axioms ones_join
#print axioms channelCount_sum
#print axioms channels_mem
#print axioms channels_pairs
#print axioms channels_nodup
#print axioms channels_length
#print axioms channels_bits
#print axioms channels_control
end ThinMatrix.ResidualFamilyKeys
