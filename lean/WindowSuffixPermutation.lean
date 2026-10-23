import GraphWindowTransforms

set_option autoImplicit false

/-! Move the selected cyclic window to the suffix without duplicating physical
positions. The other half precedes the complement of the selected window.
This is a permutation only for ell ≤ k; the executable adapter clamps ell. -/
namespace ThinMatrix.WindowSuffixPermutation
open scoped BigOperators

/-- New coordinate order: the other half, then the rotated selected half. -/
def permutation {k : ℕ} [NeZero k] (ell : ℕ) (normal : Bool) (s : Fin k) : Equiv.Perm (Fin (2*k)) :=
  (finCongr (two_mul k)).trans <| finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr (Equiv.refl (Fin k)) (Equiv.addRight (s+Fin.ofNat k ell))).trans <|
      (if normal then (Equiv.sumComm (Fin k) (Fin k)).trans finSumFinEquiv else finSumFinEquiv).trans
        (finCongr (two_mul k).symm)

theorem split_other {k : ℕ} (i : Fin k) :
    (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).symm
      ((finCongr (two_mul k)) (BinaryWindowPartition.halfIndex true i))=Sum.inl i := by
  change Fin.addCases Sum.inl Sum.inr (Fin.castAdd k i)=Sum.inl i
  simp

theorem split_selected {k : ℕ} (i : Fin k) :
    (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).symm
      ((finCongr (two_mul k)) (BinaryWindowPartition.halfIndex false i))=Sum.inr i := by
  change Fin.addCases Sum.inl Sum.inr (Fin.natAdd k i)=Sum.inr i
  exact Fin.addCases_right i

theorem permutation_other {k : ℕ} [NeZero k] (ell : ℕ) (normal : Bool) (s : Fin k) (i : Fin k) :
    permutation ell normal s (BinaryWindowPartition.halfIndex true i)=BinaryWindowPartition.halfIndex (!normal) i := by
  simp only [permutation,Equiv.trans_apply,split_other]
  cases normal <;> apply Fin.ext <;> simp [BinaryWindowPartition.halfIndex,finSumFinEquiv,Nat.add_comm]

theorem permutation_selected {k : ℕ} [NeZero k] (ell : ℕ) (normal : Bool) (s i : Fin k) :
    permutation ell normal s (BinaryWindowPartition.halfIndex false i)=
      BinaryWindowPartition.halfIndex normal (i+(s+Fin.ofNat k ell)) := by
  simp only [permutation,Equiv.trans_apply,split_selected]
  cases normal <;> apply Fin.ext <;> simp [BinaryWindowPartition.halfIndex,finSumFinEquiv,Nat.add_comm]

def suffixIndex {k ell : ℕ} (h : ell≤2*k) (j : Fin ell) : Fin (2*k) := ⟨2*k-ell+j.val,by omega⟩

theorem permutation_suffix {k : ℕ} [NeZero k] (ell : ℕ) (he : ell≤k) (normal : Bool) (s : Fin k) (j : Fin ell) :
    permutation ell normal s (suffixIndex (he.trans (by omega)) j)=
      BinaryWindowPartition.halfIndex normal (s+Fin.ofNat k j.val) := by
  let i : Fin k := ⟨k-ell+j.val,by omega⟩
  have hi : suffixIndex (he.trans (by omega)) j=BinaryWindowPartition.halfIndex false i := by
    apply Fin.ext
    simp only [suffixIndex,BinaryWindowPartition.halfIndex,Bool.false_eq_true,↓reduceIte,i]
    omega
  rw [hi,permutation_selected]
  have hr : i+Fin.ofNat k ell=Fin.ofNat k j.val := by
    apply Fin.ext
    change (k-ell+j.val+ell%k)%k=j.val%k
    rw [Nat.add_mod_mod,show k-ell+j.val+ell=k+j.val by omega]
    simp
  rw [show i+(s+Fin.ofNat k ell)=s+(i+Fin.ofNat k ell) by ac_rfl,hr]

/-- Equal integer window weights before and after the physical permutation. -/
theorem suffix_weight {k : ℕ} [NeZero k] (ell : ℕ) (he : ell≤k) (normal : Bool) (s : Fin k)
    (word : CroppedGroupedSuffix.Word (2*k)) :
    (∑ j : Fin ell, if word (suffixIndex (he.trans (by omega)) j)=2 then 1 else 0)=
      CyclicLightWindow.weight ell (BinaryWindowPartition.bits normal
        (fun i => word ((permutation ell normal s).symm i))) s := by
  unfold CyclicLightWindow.weight BinaryWindowPartition.bits
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (permutation ell normal s).symm (permutation_suffix ell he normal s j)
  simp only [Equiv.symm_apply_apply] at h
  simp only [decide_eq_true_eq]
  exact congrArg (fun i : Fin (2*k) => if word i=2 then (1:ℕ) else 0) h

#print axioms split_other
#print axioms split_selected
#print axioms permutation_other
#print axioms permutation_selected
#print axioms permutation_suffix
#print axioms suffix_weight
end ThinMatrix.WindowSuffixPermutation
