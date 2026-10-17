import FoldedBackendExecution

/-!
# Arithmetic proof specifications for folded coefficient formation

These definitions are proof-side reference formulas. They expose flat
address quotient/remainder arithmetic and guarded stored-table reads, so a
binary coefficient producer need not execute ZMod operations or construct
Fin proof arguments. The frozen producer and its executable code are not
changed here.
-/

namespace ThinMatrix.FoldedFormationArithmetic

open Fin.CommRing
open StoredMinPlusAPSP FoldedBackendExecution

/-- A total proof-side view of a stored integer table, using guarded reads. -/
def tableRead {n : ℕ} (A : IntTable n) (i j : ℕ) : ℤ :=
  (A.toArray.getD i (Vector.replicate n 0)).toArray.getD j 0

theorem tableRead_eq {n : ℕ} (A : IntTable n) (i j : Fin n) :
    tableRead A i.val j.val = decode A i j := by
  simp only [tableRead, Array.getD, Vector.size_toArray, i.isLt, j.isLt, dif_pos,
    decode, Vector.get, Array.getInternal_eq_getElem, Fin.val_cast]

theorem fin_eq_intCast_iff {q : ℕ} [NeZero q] (coeff : Fin q) (value : ℤ) :
    coeff = (value : Fin q) ↔ (coeff.val : ℤ) = value % (q : ℤ) := by
  have hv : (((value : Fin q).val : ℕ) : ℤ) = value % (q : ℤ) := by
    rw [Fin.val_intCast]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne q))
  constructor
  · rintro rfl
    exact hv
  · intro h
    apply Fin.ext
    exact Int.ofNat_injective (h.trans hv.symm)

theorem zmod_eq_intCast_iff {d : ℕ} [NeZero d] (sigma : ZMod d) (value : ℤ) :
    sigma = (value : ZMod d) ↔ (sigma.val : ℤ) = value % (d : ℤ) := by
  constructor
  · rintro rfl
    exact ZMod.val_intCast value
  · intro h
    apply ZMod.val_injective d
    exact Int.ofNat_injective (h.trans (ZMod.val_intCast value).symm)

theorem residue_add_iff {d : ℕ} [NeZero d] (sigma : ZMod d) (value : ℤ) (a : ℕ) :
    sigma = (value : ZMod d)+(a : ZMod d) ↔
      (sigma.val : ℤ) = (value+(a : ℤ)) % (d : ℤ) := by
  simpa only [Int.cast_add, Int.cast_natCast] using
    zmod_eq_intCast_iff sigma (value+(a : ℤ))

theorem residue_sub_iff {d : ℕ} [NeZero d] (sigma : ZMod d) (value : ℤ) (w b : ℕ) :
    sigma = -(value : ZMod d)-(w : ZMod d)*(b : ZMod d) ↔
      (sigma.val : ℤ) = (-value-(w : ℤ)*(b : ℤ)) % (d : ℤ) := by
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using
    zmod_eq_intCast_iff sigma (-value-(w : ℤ)*(b : ℤ))

theorem finEquiv_val {d : ℕ} [NeZero d] (x : Fin d) :
    ((ZMod.finEquiv d) x).val = x.val := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

theorem outer_fst_val (n d : ℕ) (row : Fin (outerSize n d)) :
    ((CompactBlocks.outerEquiv n d).symm row).1.val =
      row.val / FoldedCounts.foldWidth d := rfl

theorem outer_snd_val (n d : ℕ) (row : Fin (outerSize n d)) :
    ((CompactBlocks.outerEquiv n d).symm row).2.val =
      row.val % FoldedCounts.foldWidth d := rfl

theorem middle_fst_val (h d : ℕ) [NeZero d] (middle : Fin (rawMiddle h d)) :
    ((CompactBlocks.middleEquiv h d).symm middle).1.val = middle.val / d := rfl

theorem middle_snd_val (h d : ℕ) [NeZero d] (middle : Fin (rawMiddle h d)) :
    ((CompactBlocks.middleEquiv h d).symm middle).2.val = middle.val % d := by
  exact finEquiv_val _

theorem localLeft_tableRead {n h : ℕ} (b : Fin (CompactBlocks.blockCount n h))
    (A : IntTable n) (i : Fin n) (s : Fin h) :
    CompactBlocks.localLeft b (fun i g => 3*decode A i g) i s =
      if CompactBlocks.index b s < n then
        3*tableRead A i.val (CompactBlocks.index b s) else 0 := by
  unfold CompactBlocks.localLeft
  split
  · rw [tableRead_eq A i ⟨CompactBlocks.index b s, by assumption⟩]
  · rfl

theorem localRight_tableRead {n h : ℕ} (b : Fin (CompactBlocks.blockCount n h))
    (B : IntTable n) (s : Fin h) (j : Fin n) :
    CompactBlocks.localRight b (fun g j => 3*decode B g j) s j =
      if CompactBlocks.index b s < n then
        3*tableRead B (CompactBlocks.index b s) j.val else 0 := by
  unfold CompactBlocks.localRight
  split
  · rw [tableRead_eq B ⟨CompactBlocks.index b s, by assumption⟩ j]
  · rfl

theorem rawLeft_arithmetic {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n)
    (row : Fin (outerSize n (physicalFold f)))
    (middle : Fin (rawMiddle h (physicalFold f))) (coeff : Fin f.cyclic) :
    rawLeft f b A row middle coeff =
      let d := physicalFold f
      let w := FoldedCounts.foldWidth d
      let i := row.val / w
      let a := row.val % w
      let s := middle.val / d
      let sigma := middle.val % d
      let g := b.val*h+s
      let value := if g < n then 3*tableRead A i g else 0
      if g < n ∧ (sigma : ℤ) = (value+(a : ℤ)) % (d : ℤ) ∧
        (coeff.val : ℤ) = value % (f.cyclic : ℤ) then 1 else 0 := by
  simp only [rawLeft, localLeft_tableRead, residue_add_iff, fin_eq_intCast_iff,
    CompactBlocks.index, outer_fst_val, outer_snd_val, middle_fst_val, middle_snd_val]

theorem rawRight_arithmetic {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n)
    (middle : Fin (rawMiddle h (physicalFold f)))
    (column : Fin (outerSize n (physicalFold f))) (coeff : Fin f.cyclic) :
    rawRight f b B middle column coeff =
      let d := physicalFold f
      let w := FoldedCounts.foldWidth d
      let j := column.val / w
      let bres := column.val % w
      let s := middle.val / d
      let sigma := middle.val % d
      let g := b.val*h+s
      let value := if g < n then 3*tableRead B g j else 0
      if (sigma : ℤ) = (-value-(w : ℤ)*(bres : ℤ)) % (d : ℤ) ∧
        (coeff.val : ℤ) = value % (f.cyclic : ℤ) then 1 else 0 := by
  simp only [rawRight, localRight_tableRead, residue_sub_iff, fin_eq_intCast_iff,
    CompactBlocks.index, outer_fst_val, outer_snd_val, middle_fst_val, middle_snd_val]

/-- Flat proof specification for every padded left coefficient, including
inactive last-block labels and all padded middle coordinates. -/
def leftReference {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n)
    (address : Fin (outerSize n (physicalFold f)*middleSize h (physicalFold f)))
    (coeff : Fin f.cyclic) : ℤ :=
  let d := physicalFold f
  let w := FoldedCounts.foldWidth d
  let D := middleSize h d
  let row := address.val / D
  let middle := address.val % D
  let i := row / w
  let a := row % w
  let s := middle / d
  let sigma := middle % d
  let g := b.val*h+s
  let value := if g < n then 3*tableRead A i g else 0
  if middle < h*d ∧ g < n ∧
      (sigma : ℤ) = (value+(a : ℤ)) % (d : ℤ) ∧
      (coeff.val : ℤ) = value % (f.cyclic : ℤ) then 1 else 0

/-- The right source deliberately retains the canonical inactive-slot
zero value; it has no separate g<n guard on its monomial. -/
def rightReference {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n)
    (address : Fin (middleSize h (physicalFold f)*outerSize n (physicalFold f)))
    (coeff : Fin f.cyclic) : ℤ :=
  let d := physicalFold f
  let w := FoldedCounts.foldWidth d
  let N := outerSize n d
  let middle := address.val / N
  let column := address.val % N
  let j := column / w
  let bres := column % w
  let s := middle / d
  let sigma := middle % d
  let g := b.val*h+s
  let value := if g < n then 3*tableRead B g j else 0
  if middle < h*d ∧
      (sigma : ℤ) = (-value-(w : ℤ)*(bres : ℤ)) % (d : ℤ) ∧
      (coeff.val : ℤ) = value % (f.cyclic : ℤ) then 1 else 0

theorem formLeft_arithmetic {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (A : IntTable n)
    (address : Fin (outerSize n (physicalFold f)*middleSize h (physicalFold f)))
    (coeff : Fin f.cyclic) :
    ((formLeft f b A).get address).get coeff = leftReference f b A address coeff := by
  simp only [formLeft, serializeLeft, Vector.get_ofFn]
  split
  · rename_i hk
    change address.val % middleSize h (physicalFold f) < h*physicalFold f at hk
    rw [rawLeft_arithmetic]
    simp only [leftReference, finProdFinEquiv, Equiv.coe_fn_symm_mk,
      Fin.divNat, Fin.modNat, hk, true_and]
  · rename_i hk
    simp only [leftReference, rawMiddle, finProdFinEquiv, Equiv.coe_fn_symm_mk,
      Fin.divNat, Fin.modNat] at hk ⊢
    simp only [hk, false_and, if_false]

theorem formRight_arithmetic {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (b : Fin (CompactBlocks.blockCount n h)) (B : IntTable n)
    (address : Fin (middleSize h (physicalFold f)*outerSize n (physicalFold f)))
    (coeff : Fin f.cyclic) :
    ((formRight f b B).get address).get coeff = rightReference f b B address coeff := by
  simp only [formRight, serializeRight, Vector.get_ofFn]
  split
  · rename_i hk
    change address.val / outerSize n (physicalFold f) < h*physicalFold f at hk
    rw [rawRight_arithmetic]
    simp only [rightReference, finProdFinEquiv, Equiv.coe_fn_symm_mk,
      Fin.divNat, Fin.modNat, hk, true_and]
  · rename_i hk
    simp only [rightReference, rawMiddle, finProdFinEquiv, Equiv.coe_fn_symm_mk,
      Fin.divNat, Fin.modNat] at hk ⊢
    simp only [hk, false_and, if_false]

end ThinMatrix.FoldedFormationArithmetic

#print axioms ThinMatrix.FoldedFormationArithmetic.formLeft_arithmetic
#print axioms ThinMatrix.FoldedFormationArithmetic.formRight_arithmetic
