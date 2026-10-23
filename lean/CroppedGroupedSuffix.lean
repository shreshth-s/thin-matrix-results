import CappedSubsetList

set_option autoImplicit false

/-!
# Exact grouped suffix transform of a cropped ternary source

The four ordinary forms are (y₁+w,y₁,y₂-w,y₂). Pair bits choose
y₁ or y₂; an activity set chooses which rows include the rare letter.
Each pair-bit group stores all capped rare supports, with signs absorbed.
The reconstruction theorem holds for arbitrary entangled source arrays.
-/
namespace ThinMatrix.CroppedGroupedSuffix
open WalshEmbedding
open scoped BigOperators

abbrev Word (n : ℕ) := Fin n → Fin 3

def pairLetter (b : Bool) : Fin 3 := if b then 1 else 0

def rare {n : ℕ} (w : Word n) : Finset (Fin n) := Finset.univ.filter (fun i => w i = 2)

def word {n : ℕ} (p : Cube n) (J : Finset (Fin n)) : Word n :=
  fun i => if i ∈ J then 2 else pairLetter (p i)

@[simp] theorem rare_word {n : ℕ} (p : Cube n) (J : Finset (Fin n)) : rare (word p J) = J := by
  ext i
  cases hp : p i <;> simp [rare,word,pairLetter,hp]

def canonicalPair {n : ℕ} (w : Word n) : Cube n := fun i => decide (w i = 1)

@[simp] theorem word_canonicalPair {n : ℕ} (w : Word n) : word (canonicalPair w) (rare w) = w := by
  funext i
  have hi := (w i).isLt
  have hw : w i = 0 ∨ w i = 1 ∨ w i = 2 := by omega
  rcases hw with h | h | h <;> simp [word,canonicalPair,rare,pairLetter,h]

variable {R : Type*} [CommRing R]

def sign (b : Bool) : R := if b then -1 else 1

def localForm (p active : Bool) (a : Fin 3) : R :=
  if a = 2 then (if active then sign p else 0)
  else if a = pairLetter p then 1 else 0

theorem localForm_sum (p active : Bool) (v : Fin 3 → R) :
    (∑ a, localForm p active a*v a) =
      if p then (if active then v 1-v 2 else v 1)
      else (if active then v 0+v 2 else v 0) := by
  cases p <;> cases active <;> simp [localForm,pairLetter,sign,Fin.sum_univ_succ,sub_eq_add_neg]

def kernel {n : ℕ} (p : Cube n) (A : Finset (Fin n)) (w : Word n) : R :=
  ∏ i, localForm (p i) (decide (i ∈ A)) (w i)

def signed {n : ℕ} (p : Cube n) (J : Finset (Fin n)) : R := ∏ i ∈ J, sign (p i)

theorem kernel_word {n : ℕ} (p : Cube n) (A J : Finset (Fin n)) :
    kernel p A (word p J) = if J ⊆ A then signed (R := R) p J else 0 := by
  by_cases hJA : J ⊆ A
  · rw [if_pos hJA]
    have hlocal (i : Fin n) :
        localForm (p i) (decide (i ∈ A)) (word p J i) =
          if i ∈ J then sign (R := R) (p i) else 1 := by
      by_cases hi : i ∈ J
      · simp [word,hi,localForm,hJA hi]
      · cases hp : p i <;> simp [word,hi,localForm,pairLetter,hp]
    simp only [kernel,hlocal,signed]
    simp
  · rw [if_neg hJA]
    obtain ⟨i,hi,hiA⟩ := Finset.not_subset.mp hJA
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [localForm,word,hi,hiA]

theorem kernel_zero_unmatched {n : ℕ} (p : Cube n) (A : Finset (Fin n)) (w : Word n)
    (hw : w ≠ word p (rare w)) : kernel (R := R) p A w = 0 := by
  have hex : ∃ i, w i ≠ word p (rare w) i := by
    by_contra! h
    exact hw (funext h)
  obtain ⟨i,hi⟩ := hex
  have hn : w i ≠ 2 := by intro h; apply hi; simp [word,rare,h]
  have hp : w i ≠ pairLetter (p i) := by
    simpa [word,rare,hn] using hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [localForm,hn,hp]

def crop {n : ℕ} (r : ℕ) (X : Word n → R) (w : Word n) : R :=
  if (rare w).card ≤ r then X w else 0

noncomputable def transform {n : ℕ} (p : Cube n) (A : Finset (Fin n)) (X : Word n → R) : R :=
  ∑ w, kernel p A w * X w

def data {n : ℕ} (p : Cube n) (X : Word n → R) (J : Finset (Fin n)) : R :=
  signed p J * X (word p J)

/-- Every compatible raw word has one rare support, recovered in the inverse
map. The copied entries in other pair-bit groups are retained separately. -/
theorem transform_cropped {n : ℕ} (r : ℕ) (p : Cube n) (A : Finset (Fin n)) (X : Word n → R) :
    transform p A (crop r X) =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r),
        if J ⊆ A then data p X J else 0 := by
  let ws : Finset (Word n) := Finset.univ.filter
    (fun w => (rare w).card ≤ r ∧ w = word p (rare w))
  have hfilter : transform p A (crop r X) = ∑ w ∈ ws, kernel p A w*X w := by
    rw [transform,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hc : (rare w).card ≤ r
    · by_cases hw : w = word p (rare w)
      · simp only [crop,if_pos hc,if_pos (And.intro hc hw)]
      · have hn : ¬((rare w).card ≤ r ∧ w = word p (rare w)) := by tauto
        simp only [crop,if_pos hc,if_neg hn,kernel_zero_unmatched p A w hw,zero_mul]
    · simp [crop,hc]
  rw [hfilter]
  apply Finset.sum_bij (fun w _ => rare w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.1⟩
  · intro w hw v hv h
    have hw' := (Finset.mem_filter.mp hw).2.2
    have hv' := (Finset.mem_filter.mp hv).2.2
    rw [hw',hv',h]
  · intro J hJ
    refine ⟨word p J,?_,rare_word p J⟩
    simp only [ws,Finset.mem_filter,Finset.mem_univ,true_and,rare_word]
    exact ⟨(Finset.mem_filter.mp hJ).2,trivial⟩
  · intro w hw
    have hw' := (Finset.mem_filter.mp hw).2.2
    rw [hw',kernel_word,rare_word]
    by_cases h : rare w ⊆ A <;> simp [h,data]

theorem transform_list {n : ℕ} (r : ℕ) (p : Cube n) (A : Finset (Fin n)) (X : Word n → R) :
    (((CappedSubsetList.array n r).toList).map
      (fun J => if J ⊆ A then data p X J else 0)).sum = transform p A (crop r X) := by
  rw [CappedSubsetList.sum_array,transform_cropped]

/-- The allocated groups include every pair-bit string and every capped
support, including all copies of a raw source coordinate. -/
theorem raw_volume_le_group_volume (n r : ℕ) :
    (Finset.univ.filter (fun w : Word n => (rare w).card ≤ r)).card ≤
      2^n * CappedSubsetList.count n r := by
  let groups := (Finset.univ : Finset (Cube n)) ×ˢ
    Finset.univ.filter (fun J : Finset (Fin n) => J.card ≤ r)
  have hsurj : (Finset.univ.filter (fun w : Word n => (rare w).card ≤ r)) =
      groups.image (fun v => word v.1 v.2) := by
    ext w
    constructor
    · intro hw
      refine Finset.mem_image.mpr ⟨(canonicalPair w,rare w),?_,word_canonicalPair w⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩⟩
    · intro hw
      obtain ⟨⟨p,J⟩,h,rfl⟩ := Finset.mem_image.mp hw
      simpa using (Finset.mem_product.mp h).2
  rw [hsurj]
  have hc : groups.card = 2^n*CappedSubsetList.count n r := by
    simp only [groups,Finset.card_product,Finset.card_univ]
    rw [← CappedSubsetList.generate_toFinset,
      List.toFinset_card_of_nodup (CappedSubsetList.generate_nodup n r),CappedSubsetList.generate_length]
    simp [Cube]
  exact Finset.card_image_le.trans (le_of_eq hc)

/-- Every full mixed 4/3 prefix layer fits the duplicated final group volume.
This is a finite allocation inequality; a shared prefix-transform program and
its execution-cost connection remain separate obligations. -/
theorem allocated_layer_volume (n r P d C : ℕ) (hd : d ≤ P) :
    (4^d*3^(P-d)*(Finset.univ.filter (fun w : Word n => (rare w).card ≤ r)).card)*C ≤
      (4^P*(2^n*CappedSubsetList.count n r))*C := by
  have hp : 4^d*3^(P-d) ≤ 4^P := by
    calc
      _ ≤ 4^d*4^(P-d) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  exact Nat.mul_le_mul_right C (Nat.mul_le_mul hp (raw_volume_le_group_volume n r))

#print axioms rare_word
#print axioms word_canonicalPair
#print axioms localForm_sum
#print axioms kernel_word
#print axioms kernel_zero_unmatched
#print axioms transform_cropped
#print axioms transform_list
#print axioms raw_volume_le_group_volume
#print axioms allocated_layer_volume
end ThinMatrix.CroppedGroupedSuffix
