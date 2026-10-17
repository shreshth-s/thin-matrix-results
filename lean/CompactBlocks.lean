import CompleteAPSP
import DenseAnswers

/-!
# Compact middle blocks with original-label recovery

Original middle labels are `Fin n`. Block b has local slots `Fin h` and
slot s denotes b*h+s exactly when that original label exists. The last block
is padded by zero left entries, not by new possible witnesses. Consequently
the folded middle dimension is h*d, rather than n*d.

Finite site counts below charge complete source arrays, including padding
and every cyclic coefficient. They are formation-size and preparation-call
counts, not a theorem about extracted Lean or fast-backend running time.
-/

namespace ThinMatrix.CompactBlocks
open scoped BigOperators
open Fin.CommRing
open ThinMatrix.CyclicRing

def blockCount (n h : ℕ) : ℕ := n ⌈/⌉ h
def index {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h) : ℕ := b.val*h+s.val
def activeSlots (n h : ℕ) (b : Fin (blockCount n h)) : Finset (Fin h) :=
  Finset.univ.filter (fun s => index b s < n)
def block (n h : ℕ) (b : Fin (blockCount n h)) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k.val/h = b.val)

def enumerate {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h) : Option (Fin n) :=
  if hs : index b s < n then some ⟨index b s, hs⟩ else none

def label {n h : ℕ} (b : Fin (blockCount n h)) (s : Fin h)
    (hs : s ∈ activeSlots n h b) : Fin n :=
  ⟨index b s, (Finset.mem_filter.mp hs).2⟩

theorem block_fit (n h : ℕ) (hh : 0 < h) : n ≤ blockCount n h*h := by
  have hf : n ≤ h*(n ⌈/⌉ h) := (ceilDiv_le_iff_le_mul hh).mp le_rfl
  simpa [blockCount, Nat.mul_comm] using hf

def blockOf {n h : ℕ} (hh : 0 < h) (k : Fin n) : Fin (blockCount n h) :=
  ⟨k.val/h, (Nat.div_lt_iff_lt_mul hh).mpr (k.isLt.trans_le (block_fit n h hh))⟩
def slotOf {n h : ℕ} (hh : 0 < h) (k : Fin n) : Fin h :=
  ⟨k.val%h, Nat.mod_lt _ hh⟩

theorem index_recovery {n h : ℕ} (hh : 0 < h) (k : Fin n) :
    index (blockOf hh k) (slotOf hh k) = k.val := by
  simp only [index, blockOf, slotOf]
  simpa [Nat.mul_comm] using Nat.div_add_mod k.val h

theorem slotOf_active {n h : ℕ} (hh : 0 < h) (k : Fin n) :
    slotOf hh k ∈ activeSlots n h (blockOf hh k) := by
  simp [activeSlots, index_recovery hh k]

theorem enumerate_recovery {n h : ℕ} (hh : 0 < h) (k : Fin n) :
    enumerate (blockOf hh k) (slotOf hh k) = some k := by
  simp [enumerate, index_recovery hh k, k.isLt]

theorem label_recovery {n h : ℕ} (hh : 0 < h) (k : Fin n) :
    label (blockOf hh k) (slotOf hh k) (slotOf_active hh k) = k := by
  apply Fin.ext
  exact index_recovery hh k

theorem label_injective {n h : ℕ} (b : Fin (blockCount n h))
    {s t : Fin h} {hs : s ∈ activeSlots n h b} {ht : t ∈ activeSlots n h b}
    (he : label b s hs = label b t ht) : s = t := by
  apply Fin.ext
  have hv := congrArg Fin.val he
  change b.val*h+s.val = b.val*h+t.val at hv
  omega

theorem label_in_block {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h))
    (s : Fin h) (hs : s ∈ activeSlots n h b) : label b s hs ∈ block n h b := by
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, label, index]
  rw [Nat.mul_comm b.val h, Nat.mul_add_div hh]
  simp [Nat.div_eq_of_lt s.isLt]

theorem label_surjective {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h))
    (k : Fin n) (hk : k ∈ block n h b) :
    ∃ s, ∃ hs : s ∈ activeSlots n h b, label b s hs = k := by
  have hk' : k.val/h = b.val := (Finset.mem_filter.mp hk).2
  let s := slotOf hh k
  have hi : index b s = k.val := by
    change b.val*h+k.val%h = k.val
    rw [← hk']
    simpa [Nat.mul_comm] using Nat.div_add_mod k.val h
  have hs : s ∈ activeSlots n h b := by simp [activeSlots, hi]
  exact ⟨s, hs, Fin.ext hi⟩

theorem active_card_eq_block {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h)) :
    (activeSlots n h b).card = (block n h b).card :=
  Finset.card_bij (fun s hs => label b s hs) (label_in_block hh b)
    (fun _ _ _ _ he => label_injective b he) (label_surjective hh b)

theorem block_card_le {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h)) :
    (block n h b).card ≤ h := by
  rw [← active_card_eq_block hh b]
  exact (Finset.card_le_univ _).trans (by simp)

theorem blocks_cover {n h : ℕ} (hh : 0 < h) (k : Fin n) :
    ∃ b : Fin (blockCount n h), k ∈ block n h b :=
  ⟨blockOf hh k, by simp [block, blockOf]⟩

theorem blocks_disjoint {n h : ℕ} {b c : Fin (blockCount n h)} {k : Fin n}
    (hb : k ∈ block n h b) (hc : k ∈ block n h c) : b = c := by
  apply Fin.ext
  exact ((Finset.mem_filter.mp hb).2.symm).trans (Finset.mem_filter.mp hc).2

variable {I J : Type*}

def localLeft {n h : ℕ} (b : Fin (blockCount n h)) (A : I → Fin n → ℤ) : I → Fin h → ℤ :=
  fun i s => if hs : index b s < n then A i ⟨index b s, hs⟩ else 0
def localRight {n h : ℕ} (b : Fin (blockCount n h)) (B : Fin n → J → ℤ) : Fin h → J → ℤ :=
  fun s j => if hs : index b s < n then B ⟨index b s, hs⟩ j else 0

theorem localLeft_label {n h : ℕ} (b : Fin (blockCount n h)) (A : I → Fin n → ℤ)
    (i : I) (s : Fin h) (hs : s ∈ activeSlots n h b) :
    localLeft b A i s = A i (label b s hs) := by
  simp [localLeft, label, (Finset.mem_filter.mp hs).2]
theorem localRight_label {n h : ℕ} (b : Fin (blockCount n h)) (B : Fin n → J → ℤ)
    (s : Fin h) (j : J) (hs : s ∈ activeSlots n h b) :
    localRight b B s j = B (label b s hs) j := by
  simp [localRight, label, (Finset.mem_filter.mp hs).2]

/-- The two original signed edge values and the target survive label
compaction exactly; this is stronger than just preserving a modular test. -/
theorem local_signed_sum {n h : ℕ} (b : Fin (blockCount n h))
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (i : I) (j : J) (s : Fin h) (hs : s ∈ activeSlots n h b) (w : Fin 3) :
    localLeft b A i s+localRight b B s j+T i j-CompleteAPSP.windowValue w =
      A i (label b s hs)+B (label b s hs) j+T i j-CompleteAPSP.windowValue w := by
  rw [localLeft_label b A i s hs, localRight_label b B s j hs]

theorem compact_witness_iff {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h))
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (i : I) (j : J) (w : Fin 3) :
    (∃ s ∈ activeSlots n h b, localLeft b A i s+localRight b B s j+T i j = CompleteAPSP.windowValue w) ↔
    ∃ k ∈ block n h b, A i k+B k j+T i j = CompleteAPSP.windowValue w := by
  constructor
  · rintro ⟨s, hs, hz⟩
    refine ⟨label b s hs, label_in_block hh b s hs, ?_⟩
    simpa only [localLeft_label b A i s hs, localRight_label b B s j hs] using hz
  · rintro ⟨k, hk, hz⟩
    obtain ⟨s, hs, he⟩ := label_surjective hh b k hk
    refine ⟨s, hs, ?_⟩
    simpa only [localLeft_label b A i s hs, localRight_label b B s j hs, he] using hz

theorem compact_count {n h : ℕ} (hh : 0 < h) (b : Fin (blockCount n h))
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (m : ℕ) (i : I) (j : J) (w : Fin 3) :
    ((activeSlots n h b).filter (fun s => (m : ℤ) ∣
      localLeft b A i s+localRight b B s j+T i j-CompleteAPSP.windowValue w)).card =
    ((block n h b).filter (fun k => (m : ℤ) ∣
      A i k+B k j+T i j-CompleteAPSP.windowValue w)).card := by
  apply Finset.card_bij (fun s hs => label b s (Finset.mem_filter.mp hs).1)
  · intro s hs
    have ha := (Finset.mem_filter.mp hs).1
    exact Finset.mem_filter.mpr ⟨label_in_block hh b s ha, by
      simpa only [local_signed_sum b A B T i j s ha w] using (Finset.mem_filter.mp hs).2⟩
  · intro s hs t ht he
    exact label_injective b he
  · intro k hk
    obtain ⟨s, hs, he⟩ := label_surjective hh b k (Finset.mem_filter.mp hk).1
    have hp : (m : ℤ) ∣ localLeft b A i s+localRight b B s j+T i j-CompleteAPSP.windowValue w := by
      rw [local_signed_sum b A B T i j s hs w, he]
      exact (Finset.mem_filter.mp hk).2
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩, he⟩

theorem padded_left_zero {n h d q : ℕ} [NeZero d] [NeZero q]
    (b : Fin (blockCount n h)) (A : I → Fin n → ℤ)
    (row : I × Fin (FoldedCounts.foldWidth d)) (s : Fin h) (sigma : ZMod d)
    (hs : s ∉ activeSlots n h b) :
    CompleteAPSP.leftEncoded d q (activeSlots n h b) (localLeft b A) row (s,sigma) = 0 := by
  funext r
  simp [CompleteAPSP.leftEncoded, hs, zero_coeff]

theorem encoded_left_bound {n h d q : ℕ} [NeZero d] [NeZero q]
    (b : Fin (blockCount n h)) (A : I → Fin n → ℤ)
    (row : I × Fin (FoldedCounts.foldWidth d)) (middle : Fin h × ZMod d) (r : Fin q) :
    (CompleteAPSP.leftEncoded d q (activeSlots n h b) (localLeft b A) row middle r).natAbs ≤ 1 := by
  unfold CompleteAPSP.leftEncoded
  split_ifs <;> norm_num

theorem encoded_right_bound {n h d q : ℕ} [NeZero d] [NeZero q]
    (b : Fin (blockCount n h)) (B : Fin n → J → ℤ)
    (middle : Fin h × ZMod d) (column : J × Fin (FoldedCounts.foldWidth d)) (r : Fin q) :
    (CompleteAPSP.rightEncoded d q (localRight b B) middle column r).natAbs ≤ 1 := by
  unfold CompleteAPSP.rightEncoded
  split_ifs <;> norm_num

/-- The compact folded coefficient counts original labels, not padding slots. -/
theorem compact_folded_count {n h m : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : CompleteAPSP.Factorization m)
    (b : Fin (blockCount n h)) (A : I → Fin n → ℤ) (B : Fin n → J → ℤ)
    (T : I → J → ℤ) (i : I) (j : J) (w : Fin 3) :
    CompleteAPSP.foldedCount backend f (activeSlots n h b) (localLeft b A) (localRight b B)
      (fun i j => T i j-CompleteAPSP.windowValue w) i j =
    ((block n h b).filter (fun k => (m : ℤ) ∣ A i k+B k j+T i j-CompleteAPSP.windowValue w)).card := by
  rw [CompleteAPSP.foldedCount_correct]
  simpa only [add_sub_assoc] using compact_count hh b A B T m i j w

/-- The controller modulus is d*q. The backend has the literal physical
modulus (3*d)*q and requires the cyclic factor to exclude three. -/
structure PhysicalFactorization (m : ℕ) where
  folded : ℕ
  cyclic : ℕ
  folded_pos : 0 < folded
  cyclic_pos : 0 < cyclic
  coprime : (3*folded).Coprime cyclic
  product : folded*cyclic = m

def PhysicalFactorization.physical {m : ℕ} (f : PhysicalFactorization m) :
    CompleteAPSP.Factorization (3*m) :=
  ⟨3*f.folded, f.cyclic, Nat.mul_pos (by decide) f.folded_pos, f.cyclic_pos,
    f.coprime, by
      calc
        3*f.folded*f.cyclic = 3*(f.folded*f.cyclic) := Nat.mul_assoc _ _ _
        _ = 3*m := congrArg (fun a => 3*a) f.product⟩

abbrev PhysicalPlan := ∀ m : ℕ, m ≠ 0 → PhysicalFactorization m
def scalarPhysicalPlan : PhysicalPlan :=
  fun m hm => ⟨m, 1, Nat.pos_of_ne_zero hm, by decide, by simp, by simp⟩

theorem cyclic_excludes_three {m : ℕ} (f : PhysicalFactorization m) : Nat.Coprime 3 f.cyclic :=
  (Nat.coprime_mul_iff_left.mp f.coprime).1

theorem localLeft_scale {n h : ℕ} (b : Fin (blockCount n h)) (A : I → Fin n → ℤ)
    (i : I) (s : Fin h) : localLeft b (fun i k => 3*A i k) i s = 3*localLeft b A i s := by
  unfold localLeft
  split_ifs <;> simp
theorem localRight_scale {n h : ℕ} (b : Fin (blockCount n h)) (B : Fin n → J → ℤ)
    (s : Fin h) (j : J) : localRight b (fun k j => 3*B k j) s j = 3*localRight b B s j := by
  unfold localRight
  split_ifs <;> simp

theorem physical_divisibility (m : ℕ) (z : ℤ) : ((3*m : ℕ) : ℤ) ∣ 3*z ↔ (m : ℤ) ∣ z := by
  push_cast
  exact Int.mul_dvd_mul_iff_left (by decide)

/-! Cached compact count tables and their composite/APSP composition. -/

def preparedProducts {n h m : ℕ}
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : CompleteAPSP.Factorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) :
    Array (Matrix (I × Fin (FoldedCounts.foldWidth f.d))
      (J × Fin (FoldedCounts.foldWidth f.d)) (Cyclic f.q)) := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  exact Array.ofFn (fun b : Fin (blockCount n h) => backend.product f.d f.q
    (CompleteAPSP.leftEncoded f.d f.q (activeSlots n h b) (localLeft b A))
    (CompleteAPSP.rightEncoded f.d f.q (localRight b B)))

theorem preparedProducts_size {n h m : ℕ}
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : CompleteAPSP.Factorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) :
    (preparedProducts backend f A B).size = blockCount n h := Array.size_ofFn

def preparedTable {n h m : ℕ}
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : CompleteAPSP.Factorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ) :
    CompleteAPSP.Incidence I J (Fin (blockCount n h)) → ℕ := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  let products := preparedProducts backend f A B
  exact fun x =>
    let target := T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2
    let C := products[x.2.1.val]'(by
      simp only [products, preparedProducts_size]
      exact x.2.1.isLt)
    (C (x.1.1, FoldedCounts.residueLow (target : ZMod f.d))
      (x.1.2, FoldedCounts.residueHigh (target : ZMod f.d)) ((-target : ℤ) : Fin f.q)).toNat

theorem preparedTable_correct {n h m : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : CompleteAPSP.Factorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (x : CompleteAPSP.Incidence I J (Fin (blockCount n h))) :
    preparedTable backend f A B T x = ((block n h x.2.1).filter (fun k =>
      (m : ℤ) ∣ A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2)).card := by
  have he : preparedTable backend f A B T x = CompleteAPSP.foldedCount backend f
      (activeSlots n h x.2.1) (localLeft x.2.1 A) (localRight x.2.1 B)
      (fun i j => T i j-CompleteAPSP.windowValue x.2.2) x.1.1 x.1.2 := by
    simp only [preparedTable, preparedProducts, Array.getElem_ofFn]
    rfl
  rw [he]
  exact compact_folded_count hh backend f x.2.1 A B T x.1.1 x.1.2 x.2.2

/-- Scaled input values make the fixed physical factor three exact, while
the certified controller continues to count its original modulus m. -/
def physicalTable {n h m : ℕ}
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : PhysicalFactorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ) :
    CompleteAPSP.Incidence I J (Fin (blockCount n h)) → ℕ := by
  let g := f.physical
  letI : NeZero g.d := ⟨Nat.ne_of_gt g.d_pos⟩
  letI : NeZero g.q := ⟨Nat.ne_of_gt g.q_pos⟩
  let products := preparedProducts backend g (fun i k => 3*A i k) (fun k j => 3*B k j)
  exact fun x =>
    let target := 3*(T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2)
    let C := products[x.2.1.val]'(by
      simp only [products, preparedProducts_size]
      exact x.2.1.isLt)
    (C (x.1.1, FoldedCounts.residueLow (target : ZMod g.d))
      (x.1.2, FoldedCounts.residueHigh (target : ZMod g.d)) ((-target : ℤ) : Fin g.q)).toNat

theorem physicalTable_correct {n h m : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : PhysicalFactorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (x : CompleteAPSP.Incidence I J (Fin (blockCount n h))) :
    physicalTable backend f A B T x = ((block n h x.2.1).filter (fun k =>
      (m : ℤ) ∣ A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2)).card := by
  have he : physicalTable backend f A B T x = CompleteAPSP.foldedCount backend f.physical
      (activeSlots n h x.2.1) (localLeft x.2.1 (fun i k => 3*A i k))
      (localRight x.2.1 (fun k j => 3*B k j))
      (fun i j => 3*(T i j-CompleteAPSP.windowValue x.2.2)) x.1.1 x.1.2 := by
    simp only [physicalTable, preparedProducts, Array.getElem_ofFn]
    rfl
  rw [he, CompleteAPSP.foldedCount_correct]
  have hf : ((activeSlots n h x.2.1).filter (fun s => ((3*m : ℕ) : ℤ) ∣
      localLeft x.2.1 (fun i k => 3*A i k) x.1.1 s+
      localRight x.2.1 (fun k j => 3*B k j) s x.1.2+
      3*(T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2))) =
      (activeSlots n h x.2.1).filter (fun s => (m : ℤ) ∣
        localLeft x.2.1 A x.1.1 s+localRight x.2.1 B s x.1.2+
        T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2) := by
    apply Finset.filter_congr
    intro s hs
    rw [localLeft_scale, localRight_scale]
    have ha : 3*localLeft x.2.1 A x.1.1 s+3*localRight x.2.1 B s x.1.2+
        3*(T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2) =
        3*(localLeft x.2.1 A x.1.1 s+localRight x.2.1 B s x.1.2+
          T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2) := by ring
    rw [ha, physical_divisibility]
  rw [hf]
  exact compact_count hh x.2.1 A B T m x.1.1 x.1.2 x.2.2

theorem physicalTable_le_block {n h m : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (f : PhysicalFactorization m)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (x : CompleteAPSP.Incidence I J (Fin (blockCount n h))) :
    physicalTable backend f A B T x ≤ h := by
  rw [physicalTable_correct hh]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (block_card_le hh _)

def countOracle {n h : ℕ} (backend : CompleteAPSP.ProductBackend I (Fin h) J)
    (plan : PhysicalPlan) (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ) :
    CompositeAlgorithm.CountOracle (CompleteAPSP.Incidence I J (Fin (blockCount n h))) where
  table m _active := if hm : m = 0 then fun x =>
      ((block n h x.2.1).filter (fun k => A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2 = 0)).card
    else physicalTable backend (plan m hm) A B T

theorem countOracle_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (plan : PhysicalPlan)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ) :
    (countOracle backend plan A B T).Correct (CompleteAPSP.incidenceInstance (block n h) A B T) := by
  intro m active x hx
  dsimp only [countOracle]
  split_ifs with hm
  · subst m
    simp [CompleteAPSP.incidenceInstance, CompositeCertification.Instance.modCount]
  · rw [physicalTable_correct hh]
    simp only [CompleteAPSP.incidenceInstance, CompositeCertification.Instance.modCount]
    exact (Finset.sum_boole (fun k : Fin n => (m : ℤ) ∣
      A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2)
      (block n h x.2.1)).symm

def solve {n h U : ℕ} {Pair : Type*} [DecidableEq Pair]
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (plan : PhysicalPlan)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (params : CompleteAPSP.Parameters h U)
    (pair : CompleteAPSP.Incidence I J (Fin (blockCount n h)) → Pair)
    (initial : Finset (CompleteAPSP.Incidence I J (Fin (blockCount n h)))) :
    CompositeAlgorithm.Result (CompleteAPSP.Incidence I J (Fin (blockCount n h))) Pair :=
  CompositeAlgorithm.solve (countOracle backend plan A B T)
    (CompleteAPSP.incidenceInstance (block n h) A B T) pair params.lam params.k params.stages params.pool initial

theorem solve_correct_and_resources {n h U : ℕ} (hh : 0 < h)
    {Pair : Type*} [DecidableEq Pair]
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (plan : PhysicalPlan)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (params : CompleteAPSP.Parameters h U)
    (hmag : ∀ (x : CompleteAPSP.Incidence I J (Fin (blockCount n h))) (v : Fin n),
      v ∈ block n h x.2.1 →
      (A x.1.1 v+B v x.1.2+T x.1.1 x.1.2-CompleteAPSP.windowValue x.2.2).natAbs ≤ U)
    (pair : CompleteAPSP.Incidence I J (Fin (blockCount n h)) → Pair)
    (initial : Finset (CompleteAPSP.Incidence I J (Fin (blockCount n h))))
    (budget : ℕ) (hbudget : h*initial.card ≤ 2^params.stages*budget) :
    let out := solve backend plan A B T params pair initial
    (∀ p, p ∈ out.answers ↔ ∃ x ∈ initial, pair x = p ∧ ∃ v ∈ block n h x.2.1,
      A x.1.1 v+B v x.1.2+T x.1.1 x.1.2 = CompleteAPSP.windowValue x.2.2) ∧
    out.calls.length ≤ params.stages*(params.k+1)*params.pool.card ∧
    CompositeAlgorithm.tableCells out.calls ≤ params.stages*(params.k+1)*params.pool.card*initial.card ∧
    out.bookkeeping ≤ 16*params.stages*(params.k+1)*(params.pool.card+1)*(initial.card+1) ∧
    out.originalSumTests ≤ budget := by
  have hdiv := (CompleteAPSP.incidenceInstance (block n h) A B T).divisorBound_of_prime_power
    params.pool params.P U params.lam params.prime params.lower params.P_pos hmag params.power
  have hc := CompositeAlgorithm.solve_correct_and_resources (countOracle backend plan A B T)
    (CompleteAPSP.incidenceInstance (block n h) A B T) (countOracle_correct hh backend plan A B T)
    pair initial params.pool params.k params.M params.lam h params.stages budget
    params.threshold params.size hdiv (fun x _ => block_card_le hh x.2.1) params.rate hbudget
  refine ⟨?_, hc.2⟩
  intro p
  simpa only [solve, CompleteAPSP.incidenceInstance, sub_eq_zero] using hc.1 p

def denseOracle {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : Fin n → Fin n → ℤ) : DenseAnswers.Output n ×
      CompositeAlgorithm.Result (CompleteAPSP.Incidence (Fin n) (Fin n) (Fin (blockCount n h)))
        (Fin n × Fin n) :=
  let result := solve backend plan A B T
    (policy (CompleteAPSP.magnitude (CompleteAPSP.incidenceInstance (block n h) A B T)))
    Prod.fst CompleteAPSP.zeroIncidences
  (DenseAnswers.build result.answers, result)

def triangleOracle {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h) :
    MinPlusReduction.TriangleOracle (Fin n) (Fin n) (Fin n) :=
  fun A B T =>
    let out := denseOracle backend plan policy A B T
    fun i j => DenseAnswers.read out.1 (i,j)

theorem triangleOracle_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h) :
    MinPlusReduction.OracleCorrect (triangleOracle backend plan policy) := by
  intro A B T i j
  let params := policy (CompleteAPSP.magnitude (CompleteAPSP.incidenceInstance (block n h) A B T))
  have hp : 1 ≤ 2^params.stages := Nat.one_le_two_pow
  have hc := solve_correct_and_resources hh backend plan A B T params
    (fun x v _ => CompleteAPSP.magnitude_bound (CompleteAPSP.incidenceInstance (block n h) A B T) x v)
    Prod.fst CompleteAPSP.zeroIncidences (h*CompleteAPSP.zeroIncidences.card)
    (by simpa using Nat.mul_le_mul_right (h*CompleteAPSP.zeroIncidences.card) hp)
  simp only [triangleOracle, denseOracle, DenseAnswers.build_correct]
  rw [hc.1 (i,j)]
  constructor
  · rintro ⟨x, hx, he, k, hk, hz⟩
    have hw : x.2.2 = CompleteAPSP.zeroWindow := (Finset.mem_filter.mp hx).2
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    exact ⟨k, by simpa only [hi, hj, hw, CompleteAPSP.windowValue_zero] using hz⟩
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := blocks_cover hh k
    refine ⟨((i,j),b,CompleteAPSP.zeroWindow), ?_, rfl, k, hb, ?_⟩
    · simp [CompleteAPSP.zeroIncidences]
    · simpa only [CompleteAPSP.windowValue_zero] using hk

theorem denseOracle_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : Fin n → Fin n → ℤ) (i j : Fin n) :
    DenseAnswers.read (denseOracle backend plan policy A B T).1 (i,j) = true ↔
      ∃ k, A i k+B k j+T i j = 0 :=
  triangleOracle_correct hh backend plan policy A B T i j

theorem denseOracle_writes {n h : ℕ}
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (A B T : Fin n → Fin n → ℤ) :
    (denseOracle backend plan policy A B T).1.2 ≤ 2*n*n :=
  DenseAnswers.build_writes_le _

def apsp {n h : ℕ} (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : APSPReduction.Graph (Fin n)) (W : ℕ) : APSPReduction.Matrix (Fin n) :=
  APSPAlgorithm.fastAPSP (triangleOracle backend plan policy) w W

theorem apsp_correct {n h : ℕ} (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : APSPReduction.Graph (Fin n)) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (hno : APSPReduction.NoNegativeCycles w) : APSPReduction.IsAPSP w (apsp backend plan policy w W) :=
  APSPAlgorithm.fastAPSP_correct (triangleOracle backend plan policy)
    (triangleOracle_correct hh backend plan policy) w W hw hno

/-! Exact finite geometry and complete source-formation sites. -/

abbrev QuerySites (n h : ℕ) := (Fin n × Fin n) × Fin (blockCount n h)
abbrev WindowQuerySites (n h : ℕ) := QuerySites n h × Fin 3
abbrev SourceSites (n h d : ℕ) :=
  ((Fin n × Fin (FoldedCounts.foldWidth d)) × (Fin h × ZMod d)) ⊕
  ((Fin h × ZMod d) × (Fin n × Fin (FoldedCounts.foldWidth d)))
abbrev CoefficientSourceSites (n h d q : ℕ) := SourceSites n h d × Fin q

theorem block_count_exact (n h : ℕ) : blockCount n h = n ⌈/⌉ h := rfl
theorem query_sites_card (n h : ℕ) : Fintype.card (QuerySites n h) = n^2*blockCount n h := by
  simp [QuerySites, pow_two]
theorem window_query_sites_card (n h : ℕ) :
    Fintype.card (WindowQuerySites n h) = 3*n^2*blockCount n h := by
  rw [Fintype.card_prod, query_sites_card, Fintype.card_fin]
  ring

theorem zero_incidence_card (n h : ℕ) :
    (CompleteAPSP.zeroIncidences (I := Fin n) (J := Fin n) (H := Fin (blockCount n h))).card =
      n^2*blockCount n h := by
  have hc : (Finset.univ : Finset (QuerySites n h)).card =
      (CompleteAPSP.zeroIncidences (I := Fin n) (J := Fin n) (H := Fin (blockCount n h))).card := by
    apply Finset.card_bij (fun x _ => (x.1,x.2,CompleteAPSP.zeroWindow))
    · intro x hx
      simp [CompleteAPSP.zeroIncidences]
    · intro x hx y hy he
      apply Prod.ext
      · exact congrArg (fun z : CompleteAPSP.Incidence (Fin n) (Fin n) (Fin (blockCount n h)) => z.1) he
      · exact congrArg (fun z => z.2.1) he
    · intro x hx
      have hw := (Finset.mem_filter.mp hx).2
      refine ⟨(x.1,x.2.1), Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · exact hw.symm
  simpa only [Finset.card_univ, query_sites_card] using hc.symm

theorem compact_middle_dimension (h d : ℕ) [NeZero d] :
    Fintype.card (Fin h × ZMod d) = h*d := by simp

/-- Computable flattenings expose the literal N-by-D matrix shape for the
backend's subsequent power-of-four padding and tiling. -/
def outerEquiv (n d : ℕ) : (Fin n × Fin (FoldedCounts.foldWidth d)) ≃
    Fin (n*FoldedCounts.foldWidth d) := finProdFinEquiv
def middleEquiv (h d : ℕ) [NeZero d] : (Fin h × ZMod d) ≃ Fin (h*d) :=
  (Equiv.prodCongr (Equiv.refl _) (ZMod.finEquiv d).symm.toEquiv).trans finProdFinEquiv

theorem flattened_product {R : Type*} [AddCommMonoid R] [Mul R]
    (n h d : ℕ) [NeZero d]
    (A : Matrix (Fin n × Fin (FoldedCounts.foldWidth d)) (Fin h × ZMod d) R)
    (B : Matrix (Fin h × ZMod d) (Fin n × Fin (FoldedCounts.foldWidth d)) R) :
    Matrix.reindex (outerEquiv n d) (outerEquiv n d) (A*B) =
      Matrix.reindex (outerEquiv n d) (middleEquiv h d) A *
        Matrix.reindex (middleEquiv h d) (outerEquiv n d) B := by
  simpa only [Matrix.reindex_apply] using (Matrix.submatrix_mul_equiv A B
    (outerEquiv n d).symm (middleEquiv h d).symm (outerEquiv n d).symm).symm

/-- The complete arrays contain two N-by-D sources. All padding entries are
charged, and cyclic vectors charge all q coefficients, not just query reads. -/
theorem coefficient_source_sites_card (n h d q : ℕ) [NeZero d] :
    Fintype.card (CoefficientSourceSites n h d q) =
      2*q*(n*FoldedCounts.foldWidth d)*(h*d) := by
  simp [CoefficientSourceSites, SourceSites]
  ring

theorem physical_middle_dimension (h d : ℕ) [NeZero d] :
    Fintype.card (Fin h × ZMod (3*d)) = 3*h*d := by
  simp
  ring

theorem physical_source_sites_card (n h d q : ℕ) [NeZero d] :
    Fintype.card (CoefficientSourceSites n h (3*d) q) =
      2*q*(n*FoldedCounts.foldWidth (3*d))*(3*h*d) := by
  rw [coefficient_source_sites_card]
  ring

theorem all_block_source_sites_card (n h d q : ℕ) [NeZero d] :
    Fintype.card (Fin (blockCount n h) × CoefficientSourceSites n h (3*d) q) =
      blockCount n h*(2*q*(n*FoldedCounts.foldWidth (3*d))*(3*h*d)) := by
  rw [Fintype.card_prod, Fintype.card_fin, physical_source_sites_card]

theorem solve_preparations {n h U : ℕ} {Pair : Type*} [DecidableEq Pair]
    (backend : CompleteAPSP.ProductBackend I (Fin h) J) (plan : PhysicalPlan)
    (A : I → Fin n → ℤ) (B : Fin n → J → ℤ) (T : I → J → ℤ)
    (params : CompleteAPSP.Parameters h U)
    (pair : CompleteAPSP.Incidence I J (Fin (blockCount n h)) → Pair)
    (initial : Finset (CompleteAPSP.Incidence I J (Fin (blockCount n h)))) :
    CompleteAPSP.preparationCalls (blockCount n h) (solve backend plan A B T params pair initial).calls ≤
      params.stages*(params.k+1)*params.pool.card*blockCount n h := by
  apply CompositeAlgorithm.solve_oracleWork_bound
  intro c hc
  split_ifs <;> omega

theorem apsp_adaptive_magnitude {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (backend : CompleteAPSP.ProductBackend (Fin n) (Fin h) (Fin n))
    (plan : PhysicalPlan) (policy : CompleteAPSP.ParameterPolicy h)
    (w : APSPReduction.Graph (Fin n)) (W : ℕ) (hw : APSPReduction.EdgeBound w W) :
    ∀ q ∈ APSPAlgorithm.fastTrace (triangleOracle backend plan policy) w
      (APSPAlgorithm.globalBound n W) (APSPReduction.rounds n),
    CompleteAPSP.magnitude (CompleteAPSP.incidenceInstance (block n h) q.1 q.2.1 q.2.2) ≤ 192*n*W+40 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro q hq
  have hb := APSPAlgorithm.fastTrace_weight_bound (triangleOracle backend plan policy)
    (triangleOracle_correct hh backend plan policy) w W hw (APSPReduction.rounds n) (by simp) q
    (by simpa only [Fintype.card_fin] using hq)
  have hm := CompleteAPSP.triangle_magnitude_bound (block n h) q.1 q.2.1 q.2.2 (64*n*W+13)
    (fun i k => CompleteAPSP.natAbs_of_symmetric (by simpa using hb.1 i k))
    (fun k j => CompleteAPSP.natAbs_of_symmetric (by simpa using hb.2.1 k j))
    (fun i j => CompleteAPSP.natAbs_of_symmetric (by simpa using hb.2.2 i j))
  nlinarith

#print axioms label_recovery
#print axioms active_card_eq_block
#print axioms blocks_cover
#print axioms compact_count
#print axioms compact_witness_iff
#print axioms encoded_left_bound
#print axioms encoded_right_bound
#print axioms compact_folded_count
#print axioms physical_divisibility
#print axioms physicalTable_correct
#print axioms physicalTable_le_block
#print axioms cyclic_excludes_three
#print axioms countOracle_correct
#print axioms solve_correct_and_resources
#print axioms triangleOracle_correct
#print axioms denseOracle_correct
#print axioms denseOracle_writes
#print axioms apsp_correct
#print axioms zero_incidence_card
#print axioms physical_middle_dimension
#print axioms flattened_product
#print axioms physical_source_sites_card
#print axioms solve_preparations
#print axioms apsp_adaptive_magnitude

end ThinMatrix.CompactBlocks
