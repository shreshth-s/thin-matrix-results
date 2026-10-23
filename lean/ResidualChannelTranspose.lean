import ResidualFamilyKeys

set_option autoImplicit false

/-! Executable transpose of actual retained strict joint-channel keys. The
linear retained-key scan and both materialized halves are charged as indexed
control. This is not a constant-time lookup or binary address claim. -/
namespace ThinMatrix.ResidualChannelTranspose
open ResidualFamilyKeys BinaryGroupedCoordinates BinaryGroupedPreparation

def swap {m : ℕ} (c : Channel m) : Channel m := opposite c ++ normal c

theorem normal_swap {m : ℕ} (c : Channel m) : normal (swap c)=opposite c := (split_join _ _).1

theorem opposite_swap {m : ℕ} (c : Channel m) : opposite (swap c)=normal c := (split_join _ _).2

@[simp] theorem swap_swap {m : ℕ} (c : Channel m) : swap (swap c)=c := by
  simp only [swap,split_join,join_split]

theorem ones_swap {m : ℕ} (c : Channel m) : CappedBitPreparation.ones (swap c)=CappedBitPreparation.ones c := by
  calc
    _ = CappedBitPreparation.ones (opposite c)+CappedBitPreparation.ones (normal c) := ones_join _ _
    _ = CappedBitPreparation.ones (normal c)+CappedBitPreparation.ones (opposite c) := Nat.add_comm _ _
    _ = _ := by rw [← ones_join,join_split]

theorem swap_mem {m t : ℕ} (c : Channel m) (hc : c∈(channels m t).value) : swap c∈(channels m t).value := by
  rw [channels_mem] at hc ⊢
  rwa [ones_swap]

def locate {m N : ℕ} (keys : Vector (Channel m) N) (i : Fin N) : Run (Fin N) :=
  let key := swap (keys.get i)
  let j := keys.toList.idxOf key
  ⟨if h : j<N then ⟨j,h⟩ else i,0,(16*m+16)*keys.toArray.size+24*m+16⟩

theorem locate_get {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) (i : Fin (channelCount m t)) :
    keys.get (locate keys i).value=swap (keys.get i) := by
  have hm : keys.get i∈(channels m t).value := by
    rw [← hk]
    exact List.mem_iff_get.mpr ⟨⟨i.val,by simp⟩,rfl⟩
  have hs : swap (keys.get i)∈keys.toList := by rw [hk]; exact swap_mem _ hm
  have hj : keys.toList.idxOf (swap (keys.get i))<channelCount m t := by
    simpa only [Vector.length_toList] using List.idxOf_lt_length_iff.mpr hs
  simp only [locate,hj,↓reduceDIte]
  have h := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hs)
  simpa only [Vector.getElem_toList,Vector.get_eq_getElem] using h

theorem locate_halves {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) (i : Fin (channelCount m t)) :
    normal (keys.get (locate keys i).value)=opposite (keys.get i) ∧
    opposite (keys.get (locate keys i).value)=normal (keys.get i) := by
  rw [locate_get keys hk]
  exact ⟨normal_swap _,opposite_swap _⟩

theorem locate_bits {m N : ℕ} (keys : Vector (Channel m) N) (i : Fin N) : (locate keys i).bitSteps=0 := rfl

def budget (m N : ℕ) : ℕ := (16*m+16)*N+24*m+16

theorem locate_control {m N : ℕ} (keys : Vector (Channel m) N) (i : Fin N) :
    (locate keys i).control=budget m N := by simp [locate,budget]

def prepare {m N : ℕ} (keys : Vector (Channel m) N) : Run (Vector (Fin N) N) := tabulate keys (locate keys)

@[simp] theorem prepare_get {m N : ℕ} (keys : Vector (Channel m) N) (i : Fin N) :
    (prepare keys).value.get i=(locate keys i).value := tabulate_get _ _ _

theorem prepare_bits {m N : ℕ} (keys : Vector (Channel m) N) : (prepare keys).bitSteps=0 := by
  simp only [prepare,tabulate_bits_eq,locate_bits,Finset.sum_const_zero]

theorem prepare_control {m N : ℕ} (keys : Vector (Channel m) N) :
    (prepare keys).control≤N*(budget m N+32)+8 := tabulate_control _ _ (fun i => (locate_control keys i).le)

theorem locate_involutive {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) : Function.Involutive (fun i => (locate keys i).value) := by
  intro i
  have he : keys.get (locate keys (locate keys i).value).value=keys.get i := by
    rw [locate_get keys hk,locate_get keys hk,swap_swap]
  have hn : keys.toList.Nodup := by rw [hk]; exact channels_nodup m t
  have hf := hn.injective_get (show keys.toList.get ⟨(locate keys (locate keys i).value).value.val,by simp⟩=
      keys.toList.get ⟨i.val,by simp⟩ from he)
  exact Fin.ext (congrArg (fun j : Fin keys.toList.length => j.val) hf)

#print axioms locate_involutive

#print axioms normal_swap
#print axioms opposite_swap
#print axioms swap_swap
#print axioms ones_swap
#print axioms swap_mem
#print axioms locate_get
#print axioms locate_halves
#print axioms locate_bits
#print axioms locate_control
#print axioms prepare_get
#print axioms prepare_bits
#print axioms prepare_control
end ThinMatrix.ResidualChannelTranspose
