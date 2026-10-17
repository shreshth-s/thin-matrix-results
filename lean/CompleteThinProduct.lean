import TensorContraction
import HighBoxDP
import RawWordBijection
import CyclicRing
import GoodMapEmbedding

/-!
# Complete finite thin-product query

The low polynomial functional and the stored physical high-box recurrence
are composed here before applying the raw Walsh/source embedding.  The
sources, their same-run filters, and every full physical leaf remain the
actual finite arrays.  Integer cyclic decoding divides only the complete
numerator.  These are finite program/table correctness statements; their
asymptotic execution and bit costs are separate obligations.
-/

namespace ThinMatrix.CompleteThinProduct

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ThinMatrix.TensorContraction
open ThinMatrix.HighBoxDP
open ThinMatrix.WalshEmbedding

variable {R : Type*} [CommRing R]
variable {A B : Type*} [Fintype A] [Fintype B]

/-- A full physical leaf is the product of the two arbitrary raw transforms. -/
def globalLeaf {n : ℕ} (X : A → R) (Y : B → R)
    (f : Fin n → Fin 5 → A → R) (g : Fin n → Fin 5 → B → R)
    (v : LeafWord n) : R :=
  (∑ a, X a * ∏ i, f i (v i) a) * (∑ b, Y b * ∏ i, g i (v i) b)

/-- Label four is private; the full five-label sum is the inner kernel. -/
def privateKernel {n : ℕ} (f : Fin n → Fin 5 → A → R)
    (g : Fin n → Fin 5 → B → R) (i : Fin n) (a : A) (b : B) : R :=
  f i 4 a * g i 4 b

def fullKernel {n : ℕ} (f : Fin n → Fin 5 → A → R)
    (g : Fin n → Fin 5 → B → R) (i : Fin n) (a : A) (b : B) : R :=
  ∑ l : Fin 5, f i l a * g i l b

omit [Fintype A] [Fintype B] in
theorem ordinaryKernel_eq {n : ℕ} (f : Fin n → Fin 5 → A → R)
    (g : Fin n → Fin 5 → B → R) (i : Fin n) (a : A) (b : B) :
    fullKernel f g i a b - privateKernel f g i a b =
      ∑ l : Fin 4, f i l.castSucc a * g i l.castSucc b := by
  unfold fullKernel privateKernel
  rw [Fin.sum_univ_castSucc]
  change (∑ l : Fin 4, f i l.castSucc a * g i l.castSucc b) +
    f i 4 a * g i 4 b - f i 4 a * g i 4 b = _
  ring

/-- The complete generic rank-five query, with compatible leaves rather than
an unconnected symbolic high polynomial.  This also permits the physical
halves to swap normal and opposite roles. -/
theorem full_query_eq_low_add_compatible_leaves (k t : ℕ) (ht : t ≤ k)
    (X : A → R) (Y : B → R)
    (f : Fin k → Fin 5 → A → R) (g : Fin k → Fin 5 → B → R) :
    bilinear X Y (fun a b => ∏ i, fullKernel f g i a b) =
      weightedLow k t (pencilQuery k X Y (privateKernel f g) (fullKernel f g)) +
      ((ThinMatrix.OrderedBoxes.orderedBoxMasks t k).map (fun ms =>
        ∑ labels ∈ ThinMatrix.OrderedBoxes.full5CompatibleLabels
          (fun i : Fin (List.finRange k).reverse.length => ms[i.val]?.getD none),
          (∑ a, X a * ∏ i : Fin (List.finRange k).reverse.length,
            f (List.finRange k).reverse[i] (labels i) a) *
          (∑ b, Y b * ∏ i : Fin (List.finRange k).reverse.length,
            g (List.finRange k).reverse[i] (labels i) b))).sum := by
  rw [full_query_eq_weightedLow_add_boxes k t ht X Y]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro ms hms
  have hlen : (List.finRange k).reverse.length = ms.length := by
    rw [List.length_reverse, List.length_finRange,
      (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1]
  simp_rw [ordinaryKernel_eq]
  exact box_contraction_compatible_leaves X Y f g _ ms hlen

noncomputable def extendLeaf {k n : ℕ} (e : Fin k ↪o Fin n)
    (outside : Fin n → Fin 4) (labels : Fin k → Fin 5) : Fin n → Fin 5 := fun i =>
  if h : ∃ j, e j = i then labels (Classical.choose h) else (outside i).castSucc

@[simp] theorem extendLeaf_at {k n : ℕ} (e : Fin k ↪o Fin n)
    (outside : Fin n → Fin 4) (labels : Fin k → Fin 5) (j : Fin k) :
    extendLeaf e outside labels (e j) = labels j := by
  have h : ∃ a, e a = e j := ⟨j,rfl⟩
  simp only [extendLeaf, dif_pos h]
  congr 1
  exact e.injective (Classical.choose_spec h)

@[simp] theorem extendLeaf_outside {k n : ℕ} (e : Fin k ↪o Fin n)
    (outside : Fin n → Fin 4) (labels : Fin k → Fin 5) (i : Fin n)
    (hi : i ∉ HighBoxDP.embeddedSupport e) :
    extendLeaf e outside labels i = (outside i).castSucc := by
  have hn : ¬ ∃ j, e j = i := by simpa [HighBoxDP.embeddedSupport] using hi
  simp [extendLeaf, hn]

theorem extendLeaf_selectedCompatible_iff {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) (outside : Fin n → Fin 4) (labels : Fin k → Fin 5) :
    HighBoxDP.SelectedCompatible (HighBoxDP.embeddedMask e mask)
      (HighBoxDP.embeddedSupport e) outside (extendLeaf e outside labels) ↔
      HighBoxDP.MaskCompatible mask labels := by
  constructor
  · intro h j
    have hi := h.1 (e j)
    simpa only [HighBoxDP.embeddedMask_at, extendLeaf_at] using hi
  · intro h
    refine ⟨?_, fun i hi => extendLeaf_outside e outside labels i hi⟩
    intro i
    by_cases hi : i ∈ HighBoxDP.embeddedSupport e
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa only [HighBoxDP.embeddedMask_at, extendLeaf_at] using h j
    · rw [HighBoxDP.embeddedMask_outside e mask i hi, extendLeaf_outside e outside labels i hi]
      exact (outside i).isLt

theorem extendLeaf_restrict {k n : ℕ} (e : Fin k ↪o Fin n)
    (mask : Fin k → Option Bool) (outside : Fin n → Fin 4) (v : Fin n → Fin 5)
    (hv : HighBoxDP.SelectedCompatible (HighBoxDP.embeddedMask e mask)
      (HighBoxDP.embeddedSupport e) outside v) :
    extendLeaf e outside (fun j => v (e j)) = v := by
  funext i
  by_cases hi : i ∈ HighBoxDP.embeddedSupport e
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simp
  · rw [extendLeaf_outside e outside _ i hi, hv.2 i hi]

theorem sum_extendLeaf_eq_selected {k n : ℕ} {R : Type*} [AddCommMonoid R]
    (e : Fin k ↪o Fin n) (mask : Fin k → Option Bool) (outside : Fin n → Fin 4)
    (leaf : (Fin n → Fin 5) → R) :
    (∑ labels ∈ OrderedBoxes.full5CompatibleLabels mask, leaf (extendLeaf e outside labels)) =
      ∑ v : Fin n → Fin 5,
        if HighBoxDP.SelectedCompatible (HighBoxDP.embeddedMask e mask)
          (HighBoxDP.embeddedSupport e) outside v then leaf v else 0 := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin 5 =>
        HighBoxDP.SelectedCompatible (HighBoxDP.embeddedMask e mask)
          (HighBoxDP.embeddedSupport e) outside v), leaf v := by
      refine Finset.sum_bij (fun labels _ => extendLeaf e outside labels) ?_ ?_ ?_ ?_
      · intro labels hl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, (extendLeaf_selectedCompatible_iff e mask outside labels).mpr ?_⟩
        exact (HighBoxDP.maskCompatible_iff_mem mask labels).mpr hl
      · intro l₁ h₁ l₂ h₂ he
        funext j
        have hh := congrFun he (e j)
        simpa only [extendLeaf_at] using hh
      · intro v hv
        have hc := (Finset.mem_filter.mp hv).2
        refine ⟨(fun j => v (e j)), ?_, extendLeaf_restrict e mask outside v hc⟩
        apply (HighBoxDP.maskCompatible_iff_mem mask _).mp
        have hh := (extendLeaf_selectedCompatible_iff e mask outside (fun j => v (e j))).mp
        exact hh (by rw [extendLeaf_restrict e mask outside v hc]; exact hc)
      · intro labels hl; rfl
    _ = _ := by rw [Finset.sum_filter]

theorem outside_mul_inner_eq_global {k n : ℕ} {R : Type*} [CommMonoid R]
    (e : Fin k ↪o Fin n) (outside : Fin n → Fin 4) (labels : Fin k → Fin 5)
    (F : Fin n → Fin 5 → R) :
    (∏ i ∈ (HighBoxDP.embeddedSupport e)ᶜ, F i (outside i).castSucc) *
        (∏ j : Fin k, F (e j) (labels j)) =
      ∏ i : Fin n, F i (extendLeaf e outside labels i) := by
  classical
  have hs : (∏ i ∈ HighBoxDP.embeddedSupport e,
      F i (extendLeaf e outside labels i)) = ∏ j : Fin k, F (e j) (labels j) := by
    rw [HighBoxDP.embeddedSupport,
      Finset.prod_image (fun a _ b _ h => e.injective h)]
    simp only [extendLeaf_at]
  have ho : (∏ i ∈ (HighBoxDP.embeddedSupport e)ᶜ,
      F i (extendLeaf e outside labels i)) =
        ∏ i ∈ (HighBoxDP.embeddedSupport e)ᶜ, F i (outside i).castSucc := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [extendLeaf_outside e outside labels i (Finset.mem_compl.mp hi)]
  rw [← ho, ← hs]
  exact Finset.prod_compl_mul_prod _ _



 def physicalLeft {L : ℕ} (i : Fin L) : Fin (2*L) := ⟨i.val, by omega⟩
 def physicalRight {L : ℕ} (i : Fin L) : Fin (2*L) := ⟨L+i.val, by omega⟩

 theorem physicalLeft_injective {L : ℕ} : Function.Injective (@physicalLeft L) := by
   intro i j h
   apply Fin.ext
   simpa [physicalLeft] using congrArg (fun x : Fin (2*L) => x.val) h
 theorem physicalRight_injective {L : ℕ} : Function.Injective (@physicalRight L) := by
   intro i j h
   apply Fin.ext
   have h' := congrArg Fin.val h
   simpa [physicalRight] using h'

 def physicalSupport {L : ℕ} (QL QR : Finset (Fin L)) : Finset (Fin (2*L)) :=
   QL.image physicalLeft ∪ QR.image physicalRight

 theorem physicalSupport_disjoint {L : ℕ} (QL QR : Finset (Fin L)) :
     Disjoint (QL.image physicalLeft) (QR.image physicalRight) := by
   apply Finset.disjoint_left.mpr
   intro x hx hy
   obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
   obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hy
   have h := congrArg Fin.val (hix.trans hjx.symm)
   simp only [physicalLeft, physicalRight] at h
   omega

 theorem physicalSupport_card {L m : ℕ} (QL QR : Finset (Fin L))
     (hQL : QL.card=m) (hQR : QR.card=m) :
     (physicalSupport QL QR).card = 2*m := by
   rw [physicalSupport, Finset.card_union_of_disjoint (physicalSupport_disjoint QL QR)]
   rw [Finset.card_image_of_injective _ physicalLeft_injective,
       Finset.card_image_of_injective _ physicalRight_injective, hQL, hQR]
   omega

 theorem physicalSupport_left {L : ℕ} (QL QR : Finset (Fin L)) :
     (physicalSupport QL QR).filter (fun i => i.val<L) = QL.image physicalLeft := by
   rw [physicalSupport, Finset.filter_union, Finset.filter_image, Finset.filter_image]
   simp [physicalLeft, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L _)]

 theorem physicalSupport_right {L : ℕ} (QL QR : Finset (Fin L)) :
     (physicalSupport QL QR).filter (fun i => L ≤ i.val) = QR.image physicalRight := by
   rw [physicalSupport, Finset.filter_union, Finset.filter_image, Finset.filter_image]
   have hz : QL.filter (fun i => L ≤ i.val) = ∅ :=
     Finset.filter_false_of_mem (fun i _ => Nat.not_le.mpr i.isLt)
   simp [physicalLeft, physicalRight, hz]

 theorem physicalSupport_left_card {L m : ℕ} (QL QR : Finset (Fin L))
     (hQL : QL.card=m) :
     ((physicalSupport QL QR).filter (fun i => i.val<L)).card=m := by
   rw [physicalSupport_left, Finset.card_image_of_injective _ physicalLeft_injective, hQL]

 theorem physicalSupport_right_card {L m : ℕ} (QL QR : Finset (Fin L))
     (hQR : QR.card=m) :
     ((physicalSupport QL QR).filter (fun i => L ≤ i.val)).card=m := by
   rw [physicalSupport_right, Finset.card_image_of_injective _ physicalRight_injective, hQR]

 noncomputable def physicalEmbedding {L m : ℕ} (QL QR : Finset (Fin L))
     (hQL : QL.card=m) (hQR : QR.card=m) : Fin (2*m) ↪o Fin (2*L) :=
   (physicalSupport QL QR).orderEmbOfFin (physicalSupport_card QL QR hQL hQR)

 theorem physicalEmbedding_support {L m : ℕ} (QL QR : Finset (Fin L))
     (hQL : QL.card=m) (hQR : QR.card=m) :
     HighBoxDP.embeddedSupport (physicalEmbedding QL QR hQL hQR) = physicalSupport QL QR := by
   exact Finset.image_orderEmbOfFin_univ _ _

 theorem prod_physical_halves {L : ℕ} {M : Type*} [CommMonoid M]
     (f : Fin (2*L) → M) :
     (∏ i, f i) = (∏ i : Fin L, f (physicalLeft i)) *
       (∏ i : Fin L, f (physicalRight i)) := by
   have heq : L+L=2*L := by omega
   rw [← Fin.prod_congr' f heq, Fin.prod_univ_add]
   rfl

 theorem physicalLeft_ne_right {L : ℕ} (i j : Fin L) : physicalLeft i ≠ physicalRight j := by
   intro h
   have hv := congrArg Fin.val h
   simp only [physicalLeft, physicalRight] at hv
   omega

 @[simp] theorem physicalLeft_mem_support {L : ℕ} (QL QR : Finset (Fin L))
     (i : Fin L) : physicalLeft i ∈ physicalSupport QL QR ↔ i ∈ QL := by
   simp only [physicalSupport, Finset.mem_union, Finset.mem_image]
   constructor
   · rintro (⟨j, hj, hji⟩ | ⟨j, _, hji⟩)
     · exact physicalLeft_injective hji ▸ hj
     · exact False.elim (physicalLeft_ne_right i j hji.symm)
   · intro hi
     exact Or.inl ⟨i, hi, rfl⟩

 @[simp] theorem physicalRight_mem_support {L : ℕ} (QL QR : Finset (Fin L))
     (i : Fin L) : physicalRight i ∈ physicalSupport QL QR ↔ i ∈ QR := by
   simp only [physicalSupport, Finset.mem_union, Finset.mem_image]
   constructor
   · rintro (⟨j, _, hji⟩ | ⟨j, hj, hji⟩)
     · exact False.elim (physicalLeft_ne_right j i hji)
     · exact physicalRight_injective hji ▸ hj
   · intro hi
     exact Or.inr ⟨i, hi, rfl⟩

 def halfLift {L : ℕ} {M : Type*} (fL fR : Fin L → M) (i : Fin (2*L)) : M :=
   if h : i.val < L then fL ⟨i.val, h⟩ else fR ⟨i.val-L, by omega⟩

 @[simp] theorem halfLift_left {L : ℕ} {M : Type*} (fL fR : Fin L → M)
     (i : Fin L) : halfLift fL fR (physicalLeft i) = fL i := by
   simp [halfLift, physicalLeft, i.isLt]

 @[simp] theorem halfLift_right {L : ℕ} {M : Type*} (fL fR : Fin L → M)
     (i : Fin L) : halfLift fL fR (physicalRight i) = fR i := by
   simp [halfLift, physicalRight, Nat.not_lt.mpr (Nat.le_add_right L i.val)]

 theorem prod_halfLift {L : ℕ} {M : Type*} [CommMonoid M]
     (fL fR : Fin L → M) : (∏ i, halfLift fL fR i) = (∏ i, fL i) * ∏ i, fR i := by
   rw [prod_physical_halves]
   simp only [halfLift_left, halfLift_right]


theorem reverse_finRange_get (k : ℕ) (i : Fin (List.finRange k).reverse.length) :
    (List.finRange k).reverse[i] = (i.cast (by simp)).rev := by
  apply Fin.ext
  simp [List.getElem_reverse, Fin.rev]
  omega

theorem reverse_finRange_prod {M : Type*} [CommMonoid M] (k : ℕ)
    (F : Fin k → Fin 5 → M)
    (labels : Fin (List.finRange k).reverse.length → Fin 5) :
    (∏ i : Fin (List.finRange k).reverse.length,
      F (List.finRange k).reverse[i] (labels i)) =
      ∏ j : Fin k, F j
        (labels (Fin.cast (show k = (List.finRange k).reverse.length from by simp) j.rev)) := by
  let e : Fin (List.finRange k).reverse.length ≃ Fin k :=
    (finCongr (by simp)).trans Fin.revPerm
  apply Fintype.prod_equiv e
  intro i
  have hget := reverse_finRange_get k i
  simp only [e, Equiv.trans_apply, finCongr_apply, Fin.revPerm_apply]
  rw [hget]
  congr 2
  simp

theorem compatible_reverse_sum {S : Type*} [AddCommMonoid S]
    (ms : List (Option Bool)) (F : (Fin ms.length → Fin 5) → S) :
    (∑ scan ∈ ThinMatrix.OrderedBoxes.full5CompatibleLabels
        (fun i : Fin (List.finRange ms.length).reverse.length => ms[i.val]?.getD none),
      F (fun j => scan (Fin.cast
        (show ms.length = (List.finRange ms.length).reverse.length from by simp) j.rev))) =
    ∑ physical ∈ ThinMatrix.OrderedBoxes.full5CompatibleLabels (reverseMask ms),
      F physical := by
  classical
  let e : Fin (List.finRange ms.length).reverse.length ≃ Fin ms.length :=
    (finCongr (by simp)).trans Fin.revPerm
  let E : (Fin (List.finRange ms.length).reverse.length → Fin 5) ≃
      (Fin ms.length → Fin 5) := Equiv.piCongrLeft (fun _ => Fin 5) e
  have he_apply (scan : Fin (List.finRange ms.length).reverse.length → Fin 5)
      (i : Fin (List.finRange ms.length).reverse.length) : E scan (e i) = scan i := by
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  have hmask (i : Fin (List.finRange ms.length).reverse.length) :
      reverseMask ms (e i) = ms[i.val]?.getD none := by
    simp [reverseMask, e]
  apply Finset.sum_equiv E
  · intro scan
    simp only [ThinMatrix.OrderedBoxes.full5CompatibleLabels, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h j
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [he_apply, hmask]
      exact h i
    · intro h i
      have hh := h (e i)
      rwa [he_apply, hmask] at hh
  · intro scan _
    apply congrArg F
    funext j
    simp [E, e, Equiv.piCongrLeft_apply]

/-- Fixed outside ordinary factors belong to the source array used by the
inner-coordinate polynomial contraction. -/
def absorbedInput {k n : ℕ} (e : Fin k ↪o Fin n)
    (outside : Fin n → Fin 4) (X : A → R) (f : Fin n → Fin 5 → A → R) : A → R :=
  fun a => X a * ∏ i ∈ (embeddedSupport e)ᶜ, f i (outside i).castSucc a

theorem absorbed_leaf_eq_global {k n : ℕ} (e : Fin k ↪o Fin n)
    (outside : Fin n → Fin 4) (X : A → R) (Y : B → R)
    (f : Fin n → Fin 5 → A → R) (g : Fin n → Fin 5 → B → R)
    (labels : Fin k → Fin 5) :
    (∑ a, absorbedInput e outside X f a * ∏ j, f (e j) (labels j) a) *
      (∑ b, absorbedInput e outside Y g b * ∏ j, g (e j) (labels j) b) =
      globalLeaf X Y f g (extendLeaf e outside labels) := by
  unfold globalLeaf absorbedInput
  congr 1 <;> apply Finset.sum_congr rfl
  · intro a _
    rw [mul_assoc, outside_mul_inner_eq_global e outside labels (fun i l => f i l a)]
  · intro b _
    rw [mul_assoc, outside_mul_inner_eq_global e outside labels (fun i l => g i l b)]

/-- A genuine high-box contraction of the outside-absorbed source arrays
is the actual stored physical table query. No leaf output equality is
assumed, and the full global source transforms stay entangled. -/
theorem inner_box_eq_stored_physical {L m t k : ℕ}
    (ms : List (Option Bool)) (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k)
    (hlen : ms.length = 2*m) (e : Fin ms.length ↪o Fin (2*L))
    (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X : A → R) (Y : B → R)
    (f : Fin (2*L) → Fin 5 → A → R) (g : Fin (2*L) → Fin 5 → B → R) :
    bilinear (absorbedInput e outside X f) (absorbedInput e outside Y g)
      (fun a b => ThinMatrix.OrderedBoxes.boxValue
        (fun j => privateKernel (fun i => f (e i)) (fun i => g (e i)) j a b)
        (fun j => fullKernel (fun i => f (e i)) (fun i => g (e i)) j a b -
          privateKernel (fun i => f (e i)) (fun i => g (e i)) j a b)
        (List.finRange ms.length).reverse ms) =
    ∑ a : SelectedAssignments (embeddedMask e (reverseMask ms)) (embeddedSupport e),
      tableAfter (globalLeaf X Y f g) (2*L+1)
        (physicalState ms hms hlen e outside hleft hright a) := by
  simp_rw [ordinaryKernel_eq]
  unfold privateKernel
  rw [box_contraction_compatible_leaves _ _ (fun i => f (e i))
    (fun i => g (e i)) (List.finRange ms.length).reverse ms (by simp)]
  have hf (a : A) (labels : Fin (List.finRange ms.length).reverse.length → Fin 5) :=
    reverse_finRange_prod ms.length (fun i l => f (e i) l a) labels
  have hg (b : B) (labels : Fin (List.finRange ms.length).reverse.length → Fin 5) :=
    reverse_finRange_prod ms.length (fun i l => g (e i) l b) labels
  simp_rw [hf, hg]
  rw [compatible_reverse_sum ms (fun labels =>
    (∑ a, absorbedInput e outside X f a * ∏ j, f (e j) (labels j) a) *
    (∑ b, absorbedInput e outside Y g b * ∏ j, g (e j) (labels j) b))]
  simp_rw [absorbed_leaf_eq_global]
  rw [sum_extendLeaf_eq_selected]
  exact (physicalState_query ms hms hlen e outside hleft hright (globalLeaf X Y f g)).symm


noncomputable def reindexEmbedding {k n : ℕ} (ms : List (Option Bool))
    (hlen : ms.length = k) (e : Fin k ↪o Fin n) : Fin ms.length ↪o Fin n :=
  (Fin.castOrderIso hlen).toOrderEmbedding.trans e

@[simp] theorem reindexEmbedding_refl {n : ℕ} (ms : List (Option Bool))
    (h : ms.length = ms.length) (e : Fin ms.length ↪o Fin n) :
    reindexEmbedding ms h e = e := by
  rfl

theorem reindexEmbedding_support {k n : ℕ} (ms : List (Option Bool))
    (hlen : ms.length = k) (e : Fin k ↪o Fin n) :
    embeddedSupport (reindexEmbedding ms hlen e) = embeddedSupport e := by
  subst k
  rfl

/-- The high query reads the fully computed physical DP table, one entry
for each ordinary key in each generated mask. -/
noncomputable def storedBox {L m t k : ℕ} (hk : k = 2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (leaf : LeafWord (2*L) → R) (ms : List (Option Bool)) : R :=
  if hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k then
    let hlen := (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1
    let e' := reindexEmbedding ms hlen e
    ∑ a : SelectedAssignments (embeddedMask e' (reverseMask ms)) (embeddedSupport e'),
      tableAfter leaf (2*L+1) (physicalState ms hms (hlen.trans hk) e' outside
        (by simpa only [e', reindexEmbedding_support] using hleft)
        (by simpa only [e', reindexEmbedding_support] using hright) a)
  else 0

theorem box_eq_storedBox {L m t k : ℕ} (hk : k = 2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X : A → R) (Y : B → R)
    (f : Fin (2*L) → Fin 5 → A → R) (g : Fin (2*L) → Fin 5 → B → R)
    (ms : List (Option Bool)) (hms : ms ∈ ThinMatrix.OrderedBoxes.orderedBoxMasks t k) :
    bilinear (absorbedInput e outside X f) (absorbedInput e outside Y g)
      (fun a b => ThinMatrix.OrderedBoxes.boxValue
        (fun j => privateKernel (fun i => f (e i)) (fun i => g (e i)) j a b)
        (fun j => fullKernel (fun i => f (e i)) (fun i => g (e i)) j a b -
          privateKernel (fun i => f (e i)) (fun i => g (e i)) j a b)
        (List.finRange k).reverse ms) =
      storedBox (t := t) hk e outside hleft hright (globalLeaf X Y f g) ms := by
  have hlen := (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape hms).1
  have hcount := hlen.trans hk
  cases hlen
  unfold storedBox
  rw [dif_pos hms]
  exact inner_box_eq_stored_physical ms hms hcount e outside hleft hright X Y f g

noncomputable def storedHigh {L m t k : ℕ} (hk : k = 2*m)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (leaf : LeafWord (2*L) → R) : R :=
  ((ThinMatrix.OrderedBoxes.orderedBoxMasks t k).map
    (storedBox (t := t) hk e outside hleft hright leaf)).sum

noncomputable def lowQuery {L t k : ℕ}
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (X : A → R) (Y : B → R)
    (f : Fin (2*L) → Fin 5 → A → R) (g : Fin (2*L) → Fin 5 → B → R) : R :=
  weightedLow k t (pencilQuery k (absorbedInput e outside X f)
    (absorbedInput e outside Y g) (privateKernel (fun i => f (e i)) (fun i => g (e i)))
    (fullKernel (fun i => f (e i)) (fun i => g (e i))))

/-- Complete finite query using the actual low polynomial contraction and
actual stored high-box DP. Both physical halves obey their source cap. -/
theorem inner_query_eq_low_add_storedHigh {L m t k : ℕ} (hk : k = 2*m) (ht : t ≤ k)
    (e : Fin k ↪o Fin (2*L)) (outside : Fin (2*L) → Fin 4)
    (hleft : ((embeddedSupport e).filter (fun i => i.val < L)).card ≤ m)
    (hright : ((embeddedSupport e).filter (fun i => L ≤ i.val)).card ≤ m)
    (X : A → R) (Y : B → R)
    (f : Fin (2*L) → Fin 5 → A → R) (g : Fin (2*L) → Fin 5 → B → R) :
    bilinear (absorbedInput e outside X f) (absorbedInput e outside Y g)
      (fun a b => ∏ i, fullKernel (fun j => f (e j)) (fun j => g (e j)) i a b) =
      lowQuery (t := t) e outside X Y f g +
        storedHigh (t := t) hk e outside hleft hright (globalLeaf X Y f g) := by
  rw [full_query_eq_weightedLow_add_boxes k t ht]
  congr 1
  unfold storedHigh
  apply congrArg List.sum
  apply List.map_congr_left
  intro ms hms
  exact box_eq_storedBox (t := t) hk e outside hleft hright X Y f g ms hms


abbrev SourceWord (L : ℕ) := (Fin L → NormalLetter) × (Fin L → OppositeLetter)

def letterIndicator {T : Type*} [DecidableEq T] (x y : T) : R := if x = y then 1 else 0

def normalForm (n : NormalLetter) : Fin 5 → R :=
  alignedLeft (letterIndicator n .x1) (letterIndicator n .x2)
    (letterIndicator n .p1) (letterIndicator n .p2)

def oppositeForm (o : OppositeLetter) : Fin 5 → R :=
  alignedRight (letterIndicator o .s) (letterIndicator o .v) (letterIndicator o .w)

omit [Fintype A] [Fintype B] in
theorem local_form_sum (n : NormalLetter) (o : OppositeLetter) :
    (∑ l : Fin 5, normalForm (R := R) n l * oppositeForm o l) = innerCoefficient n o := by
  simp only [normalForm, oppositeForm]
  rw [aligned_label_sum]
  cases n <;> cases o <;> simp [letterIndicator, innerCoefficient]

omit [Fintype A] [Fintype B] in
theorem local_swapped_sum (n : NormalLetter) (o : OppositeLetter) :
    (∑ l : Fin 5, oppositeForm (R := R) o l * normalForm n l) = innerCoefficient n o := by
  simpa only [mul_comm] using local_form_sum (R := R) n o

def fixedLabel (i j : Bool) : Fin 4 :=
  if i then (if j then 3 else 2) else (if j then 1 else 0)

omit [Fintype A] [Fintype B] in
theorem normalForm_fixed (i j : Bool) (n : NormalLetter) :
    normalForm (R := R) n (fixedLabel i j).castSucc = ordinaryNormal i j n := by
  cases i <;> cases j <;> cases n <;>
    simp [normalForm, alignedLeft, letterIndicator, fixedLabel, ordinaryNormal]

omit [Fintype A] [Fintype B] in
theorem oppositeForm_fixed (i j : Bool) (o : OppositeLetter) :
    oppositeForm (R := R) o (fixedLabel i j).castSucc = ordinaryOpposite i j o := by
  cases i <;> cases j <;> cases o <;>
    simp [oppositeForm, alignedRight, letterIndicator, fixedLabel, ordinaryOpposite]

/-- Exact physical source operators, with reversed roles in the second half. -/
def sourceF {L : ℕ} : Fin (2*L) → Fin 5 → SourceWord L → R :=
  halfLift (fun i l a => normalForm (a.1 i) l)
    (fun i l a => oppositeForm (a.2 i) l)

def sourceG {L : ℕ} : Fin (2*L) → Fin 5 → SourceWord L → R :=
  halfLift (fun i l b => oppositeForm (b.2 i) l)
    (fun i l b => normalForm (b.1 i) l)

def sourceOutside {L : ℕ} (iL iR jL jR : Cube L) : Fin (2*L) → Fin 4 :=
  halfLift (fun i => fixedLabel (iL i) (jL i)) (fun i => fixedLabel (iR i) (jR i))

omit [Fintype A] [Fintype B] in
theorem prod_physical_support {L : ℕ} {M : Type*} [CommMonoid M]
    (QL QR : Finset (Fin L)) (F : Fin (2*L) → M) :
    (∏ i ∈ physicalSupport QL QR, F i) =
      (∏ i ∈ QL, F (physicalLeft i)) * ∏ i ∈ QR, F (physicalRight i) := by
  rw [physicalSupport, Finset.prod_union (physicalSupport_disjoint QL QR)]
  rw [Finset.prod_image (fun _ _ _ _ h => physicalLeft_injective h),
    Finset.prod_image (fun _ _ _ _ h => physicalRight_injective h)]

omit [Fintype A] [Fintype B] in
theorem prod_physical_compl {L : ℕ} {M : Type*} [CommMonoid M]
    (QL QR : Finset (Fin L)) (F : Fin (2*L) → M) :
    (∏ i ∈ (physicalSupport QL QR)ᶜ, F i) =
      (∏ i ∈ QLᶜ, F (physicalLeft i)) * ∏ i ∈ QRᶜ, F (physicalRight i) := by
  have hq : (physicalSupport QL QR)ᶜ =
      Finset.univ.filter (fun i => i ∉ physicalSupport QL QR) := by ext i; simp
  rw [hq, Finset.prod_filter, prod_physical_halves]
  simp only [physicalLeft_mem_support, physicalRight_mem_support]
  have hl : (∏ i : Fin L, if i ∉ QL then F (physicalLeft i) else 1) =
      ∏ i ∈ QLᶜ, F (physicalLeft i) := by
    simpa only [Finset.mem_compl, Finset.univ_inter] using
      Finset.prod_ite_mem Finset.univ QLᶜ (fun i => F (physicalLeft i))
  have hr : (∏ i : Fin L, if i ∉ QR then F (physicalRight i) else 1) =
      ∏ i ∈ QRᶜ, F (physicalRight i) := by
    simpa only [Finset.mem_compl, Finset.univ_inter] using
      Finset.prod_ite_mem Finset.univ QRᶜ (fun i => F (physicalRight i))
  rw [hl, hr]

def outsideF {L : ℕ} (QL QR : Finset (Fin L))
    (iL iR jL jR : Cube L) (a : SourceWord L) : R :=
  (∏ i ∈ QLᶜ, ordinaryNormal (R := R) (iL i) (jL i) (a.1 i)) *
    ∏ i ∈ QRᶜ, ordinaryOpposite (R := R) (iR i) (jR i) (a.2 i)

def outsideG {L : ℕ} (QL QR : Finset (Fin L))
    (iL iR jL jR : Cube L) (b : SourceWord L) : R :=
  (∏ i ∈ QLᶜ, ordinaryOpposite (R := R) (iL i) (jL i) (b.2 i)) *
    ∏ i ∈ QRᶜ, ordinaryNormal (R := R) (iR i) (jR i) (b.1 i)

def sourceInner {L : ℕ} (QL QR : Finset (Fin L)) (a b : SourceWord L) : R :=
  (∏ i ∈ QL, innerCoefficient (R := R) (a.1 i) (b.2 i)) *
    ∏ i ∈ QR, innerCoefficient (R := R) (b.1 i) (a.2 i)

omit [Fintype A] [Fintype B] in
theorem physical_source_inner {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card = m) (hQR : QR.card = m) (a b : SourceWord L) :
    (∏ i, fullKernel (fun j => sourceF (R := R) (physicalEmbedding QL QR hQL hQR j))
      (fun j => sourceG (physicalEmbedding QL QR hQL hQR j)) i a b) = sourceInner QL QR a b := by
  change (∏ i : Fin (2*m), fullKernel sourceF sourceG (physicalEmbedding QL QR hQL hQR i) a b) = _
  have hs := Finset.prod_image (s := Finset.univ)
    (f := fun i => fullKernel (sourceF (R := R)) sourceG i a b)
    (g := physicalEmbedding QL QR hQL hQR)
    (fun _ _ _ _ h => (physicalEmbedding QL QR hQL hQR).injective h)
  rw [← hs]
  change (∏ i ∈ embeddedSupport (physicalEmbedding QL QR hQL hQR), fullKernel sourceF sourceG i a b) = _
  rw [physicalEmbedding_support, prod_physical_support]
  simp only [fullKernel, sourceF, sourceG, halfLift_left, halfLift_right,
    local_form_sum, local_swapped_sum, sourceInner]

omit [Fintype A] [Fintype B] in
theorem physical_source_outsideF {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card = m) (hQR : QR.card = m) (iL iR jL jR : Cube L) (a : SourceWord L) :
    (∏ i ∈ (embeddedSupport (physicalEmbedding QL QR hQL hQR))ᶜ,
      sourceF (R := R) i ((sourceOutside iL iR jL jR i).castSucc) a) =
      outsideF QL QR iL iR jL jR a := by
  rw [physicalEmbedding_support, prod_physical_compl]
  simp only [sourceF, sourceOutside, halfLift_left, halfLift_right,
    normalForm_fixed, oppositeForm_fixed, outsideF]

omit [Fintype A] [Fintype B] in
theorem physical_source_outsideG {L m : ℕ} (QL QR : Finset (Fin L))
    (hQL : QL.card = m) (hQR : QR.card = m) (iL iR jL jR : Cube L) (b : SourceWord L) :
    (∏ i ∈ (embeddedSupport (physicalEmbedding QL QR hQL hQR))ᶜ,
      sourceG (R := R) i ((sourceOutside iL iR jL jR i).castSucc) b) =
      outsideG QL QR iL iR jL jR b := by
  rw [physicalEmbedding_support, prod_physical_compl]
  simp only [sourceG, sourceOutside, halfLift_left, halfLift_right,
    normalForm_fixed, oppositeForm_fixed, outsideG]


omit [Fintype A] [Fintype B] in
theorem raw_half_factor {L : ℕ} (QL QR : Finset (Fin L))
    (iL iR jL jR : Cube L) (a b : SourceWord L) :
    rawHalfKernel (R := R) QL iL jL a.1 b.2 * rawHalfKernel QR iR jR b.1 a.2 =
      outsideF QL QR iL iR jL jR a * outsideG QL QR iL iR jL jR b * sourceInner QL QR a b := by
  simp only [rawHalfKernel, outsideF, outsideG, sourceInner, Finset.prod_mul_distrib]
  ring

/-- Query data contains input arrays and source operators, never an output
value or an equality with a desired matrix product. -/
structure SourceQueryData (L m k : ℕ) (R : Type*) where
  X : RawLeftInput L m k R
  Y : RawRightInput L m k R
  good : Finset (Finset (Fin L))
  gamma : Cube L → Cube m
  delta : Cube L → Cube k
  QL : Finset (Fin L)
  QR : Finset (Fin L)
  iL : Cube L
  iR : Cube L
  jL : Cube L
  jR : Cube L
  hQL : QL.card = m
  hQR : QR.card = m

namespace SourceQueryData

variable {L m k : ℕ} (d : SourceQueryData L m k R)

noncomputable def embedding : Fin (2*m) ↪o Fin (2*L) :=
  physicalEmbedding d.QL d.QR d.hQL d.hQR

def outside : Fin (2*L) → Fin 4 := sourceOutside d.iL d.iR d.jL d.jR

noncomputable def leftRun (run : ℤ) (a : SourceWord L) : R :=
  rawLeftSource d.X d.good d.gamma d.delta run a.1 a.2

noncomputable def rightRun (run : ℤ) (b : SourceWord L) : R :=
  rawRightSource d.Y d.good d.gamma d.delta run b.1 b.2

omit [CommRing R] in
theorem left_cap : ((embeddedSupport d.embedding).filter (fun i => i.val < L)).card ≤ m := by
  rw [embedding, physicalEmbedding_support, physicalSupport_left_card d.QL d.QR d.hQL]

omit [CommRing R] in
theorem right_cap : ((embeddedSupport d.embedding).filter (fun i => L ≤ i.val)).card ≤ m := by
  rw [embedding, physicalEmbedding_support, physicalSupport_right_card d.QL d.QR d.hQR]

noncomputable def lowRun (t : ℕ) (run : ℤ) : R :=
  lowQuery (t := t) d.embedding d.outside (d.leftRun run) (d.rightRun run) sourceF sourceG

noncomputable def highRun (t : ℕ) (run : ℤ) : R :=
  storedHigh (t := t) rfl d.embedding d.outside d.left_cap d.right_cap
    (globalLeaf (d.leftRun run) (d.rightRun run) sourceF sourceG)

noncomputable def residual (t : ℕ) : R :=
  ∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), d.lowRun t run

noncomputable def high (t : ℕ) : R :=
  ∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), d.highRun t run

/-- A complete numerator is computed by adding the low result to the
stored physical high results, then summing the common source runs. -/
noncomputable def numerator (t : ℕ) : R := d.residual t + d.high t

noncomputable def matrixProductEntry (aL aR : Cube k) : R :=
  ∑ h1, ∑ h2, d.X d.QL (outsideBits d.QL d.iL) aL h1 h2 *
    d.Y d.QR (outsideBits d.QR d.iR) h1 h2 aR

theorem absorbed_leftRun (run : ℤ) :
    absorbedInput d.embedding d.outside (d.leftRun run) (sourceF (R := R)) =
      fun a => d.leftRun run a * outsideF d.QL d.QR d.iL d.iR d.jL d.jR a := by
  funext a
  unfold absorbedInput embedding outside
  rw [physical_source_outsideF]

theorem absorbed_rightRun (run : ℤ) :
    absorbedInput d.embedding d.outside (d.rightRun run) (sourceG (R := R)) =
      fun b => d.rightRun run b * outsideG d.QL d.QR d.iL d.iR d.jL d.jR b := by
  funext b
  unfold absorbedInput embedding outside
  rw [physical_source_outsideG]

theorem one_run_query (t : ℕ) (ht : t ≤ 2*m) (run : ℤ) :
    bilinear
      (fun a => d.leftRun run a * outsideF d.QL d.QR d.iL d.iR d.jL d.jR a)
      (fun b => d.rightRun run b * outsideG d.QL d.QR d.iL d.iR d.jL d.jR b)
      (sourceInner d.QL d.QR) = d.lowRun t run + d.highRun t run := by
  have h := inner_query_eq_low_add_storedHigh rfl ht d.embedding d.outside
    d.left_cap d.right_cap (d.leftRun run) (d.rightRun run) (sourceF (R := R)) sourceG
  simp_rw [absorbed_leftRun, absorbed_rightRun] at h
  simpa only [embedding, physical_source_inner, lowRun, highRun] using h

/-- The degree run is shared by both raw sources before it is summed. -/
theorem same_run_contraction :
    (∑ run ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      bilinear
        (fun a => d.leftRun run a * outsideF d.QL d.QR d.iL d.iR d.jL d.jR a)
        (fun b => d.rightRun run b * outsideG d.QL d.QR d.iL d.iR d.jL d.jR b)
        (sourceInner d.QL d.QR)) =
      rawContraction d.X d.Y d.good d.gamma d.delta d.QL d.QR d.iL d.iR d.jL d.jR := by
  classical
  unfold rawContraction
  apply Finset.sum_congr rfl
  intro run _
  unfold bilinear
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [rawPairTerm, raw_half_factor d.QL d.QR d.iL d.iR d.jL d.jR (a,e) (b,c)]
  unfold leftRun rightRun
  ring

/-- Program/table composition to the genuine A3--A4 raw contraction. -/
theorem numerator_eq_rawContraction (t : ℕ) (ht : t ≤ 2*m) :
    d.numerator t = rawContraction d.X d.Y d.good d.gamma d.delta
      d.QL d.QR d.iL d.iR d.jL d.jR := by
  rw [← same_run_contraction]
  simp only [numerator, residual, high, ← Finset.sum_add_distrib, ← one_run_query d t ht]

/-- Complete low-plus-HIGH correctness for all good queried source slots.
The restricted maps and transpose locators are the original embedding
hypotheses, not a target-output equality. -/
theorem numerator_eq_scaled_product (t : ℕ) (ht : t ≤ 2*m)
    (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta = columnMap columns)
    (hjL : d.jL = transposeMap columns aR) (hjR : d.jR = transposeMap columns aL)
    (hgood : ∀ S ∈ d.good, S.card = m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) :
    d.numerator t = (4 : R)^L * d.matrixProductEntry aL aR := by
  rw [numerator_eq_rawContraction d t ht]
  rw [ThinMatrix.RawWordBijection.rawContraction_eq_survivingContraction
    d.X d.Y d.good d.gamma d.delta d.QL d.QR d.iL d.iR d.jL d.jR d.hQL d.hQR hgood]
  rw [hdelta, hjL, hjR]
  simpa only [hL, matrixProductEntry] using
    surviving_contraction_eq_scaled_product d.X d.Y d.good d.gamma columns
      d.QL d.QR d.iL d.iR aL aR d.hQL d.hQR hgL hgR maps

end SourceQueryData


section IntegerCyclicDecode

variable {L m k q : ℕ} [NeZero q]
    (d : SourceQueryData L m k (ThinMatrix.CyclicRing.Cyclic q))

/-- Every coefficient of the complete numerator is divisible by `4^L`.
No divisibility assertion is made for an isolated residual or high term. -/
theorem complete_cyclic_numerator_scale (t : ℕ) (ht : t ≤ 2*m)
    (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta = columnMap columns)
    (hjL : d.jL = transposeMap columns aR) (hjR : d.jR = transposeMap columns aL)
    (hgood : ∀ S ∈ d.good, S.card = m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) :
    d.numerator t = ThinMatrix.CyclicRing.scale ((4 : ℤ)^L) (d.matrixProductEntry aL aR) := by
  rw [ThinMatrix.CyclicRing.scale_eq_intCast_mul]
  simpa only [Int.cast_pow, Int.cast_ofNat] using
    d.numerator_eq_scaled_product t ht columns aL aR hL hdelta hjL hjR hgood hgL hgR maps

theorem complete_cyclic_coefficient_dvd (t : ℕ) (ht : t ≤ 2*m)
    (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta = columnMap columns)
    (hjL : d.jL = transposeMap columns aR) (hjR : d.jR = transposeMap columns aL)
    (hgood : ∀ S ∈ d.good, S.card = m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) (r : Fin q) :
    (4 : ℤ)^L ∣ d.numerator t r := by
  exact ThinMatrix.CyclicRing.complete_coefficient_dvd L (d.numerator t)
    (d.matrixProductEntry aL aR)
    (complete_cyclic_numerator_scale d t ht columns aL aR hL hdelta hjL hjR hgood hgL hgR maps) r

/-- The actual complete query decodes coefficientwise over the integer
cyclic ring. It first adds residual and HIGH, preserving all coefficients. -/
theorem complete_cyclic_decode (t : ℕ) (ht : t ≤ 2*m)
    (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta = columnMap columns)
    (hjL : d.jL = transposeMap columns aR) (hjR : d.jR = transposeMap columns aL)
    (hgood : ∀ S ∈ d.good, S.card = m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) :
    ThinMatrix.CyclicRing.decode L (d.residual t + d.high t) = d.matrixProductEntry aL aR := by
  exact ThinMatrix.CyclicRing.decode_residual_plus_boxes L (d.residual t) (d.high t)
    (d.matrixProductEntry aL aR)
    (complete_cyclic_numerator_scale d t ht columns aL aR hL hdelta hjL hjR hgood hgL hgR maps)

/-- Every arbitrary cyclic target, including zero, is decoded exactly. -/
theorem complete_cyclic_target (t : ℕ) (ht : t ≤ 2*m)
    (columns : Fin L → Cube k) (aL aR : Cube k)
    (hL : m+k=L) (hdelta : d.delta = columnMap columns)
    (hjL : d.jL = transposeMap columns aR) (hjR : d.jR = transposeMap columns aL)
    (hgood : ∀ S ∈ d.good, S.card = m) (hgL : d.QL ∈ d.good) (hgR : d.QR ∈ d.good)
    (maps : RestrictedGoodMaps d.QL d.QR d.gamma (columnMap columns)) (r : Fin q) :
    (d.residual t r + d.high t r) / (4 : ℤ)^L = d.matrixProductEntry aL aR r := by
  have h := congrFun
    (complete_cyclic_decode d t ht columns aL aR hL hdelta hjL hjR hgood hgL hgR maps) r
  simpa only [ThinMatrix.CyclicRing.decode, ThinMatrix.CyclicRing.add_coeff] using h

end IntegerCyclicDecode



#print axioms ThinMatrix.CompleteThinProduct.inner_box_eq_stored_physical
#print axioms ThinMatrix.CompleteThinProduct.inner_query_eq_low_add_storedHigh
#print axioms ThinMatrix.CompleteThinProduct.SourceQueryData.numerator_eq_rawContraction
#print axioms ThinMatrix.CompleteThinProduct.SourceQueryData.numerator_eq_scaled_product
#print axioms ThinMatrix.CompleteThinProduct.complete_cyclic_coefficient_dvd
#print axioms ThinMatrix.CompleteThinProduct.complete_cyclic_decode
#print axioms ThinMatrix.CompleteThinProduct.complete_cyclic_target

/-- Fully constructed source query, including the deterministic good-map
search, the actual good family, and the transpose Delta output locators. -/
noncomputable def constructedSourceQuery (L m : ℕ)
    (X : RawLeftInput L m (L-m) R) (Y : RawRightInput L m (L-m) R)
    (QL QR : Finset (Fin L))
    (hgL : QL ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (hgR : QR ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) : SourceQueryData L m (L-m) R where
  X := X
  Y := Y
  good := ThinMatrix.GoodMapEmbedding.goodSlots L m
  gamma := ThinMatrix.GoodMapEmbedding.cubeMap (ThinMatrix.GoodSetConstruction.constructGoodMaps L m).1
  delta := ThinMatrix.GoodMapEmbedding.cubeMap (ThinMatrix.GoodSetConstruction.constructGoodMaps L m).2
  QL := QL
  QR := QR
  iL := iL
  iR := iR
  jL := transposeMap (ThinMatrix.GoodMapEmbedding.boolColumns
    (ThinMatrix.GoodSetConstruction.constructGoodMaps L m).2) aR
  jR := transposeMap (ThinMatrix.GoodMapEmbedding.boolColumns
    (ThinMatrix.GoodSetConstruction.constructGoodMaps L m).2) aL
  hQL := ThinMatrix.GoodMapEmbedding.goodSlots_size L m QL hgL
  hQR := ThinMatrix.GoodMapEmbedding.goodSlots_size L m QR hgR

/-- A complete finite product-entry algorithm with no assumed restriction
bijections: the good maps and same-label sources are the constructed ones. -/
theorem constructed_complete_numerator (L m t : ℕ) (hm : m ≤ L) (ht : t ≤ 2*m)
    (X : RawLeftInput L m (L-m) R) (Y : RawRightInput L m (L-m) R)
    (QL QR : Finset (Fin L))
    (hgL : QL ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (hgR : QR ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) :
    (constructedSourceQuery L m X Y QL QR hgL hgR iL iR aL aR).numerator t =
      (4 : R)^L * ∑ h1, ∑ h2,
        X QL (outsideBits QL iL) aL h1 h2 * Y QR (outsideBits QR iR) h1 h2 aR := by
  rw [SourceQueryData.numerator_eq_rawContraction _ t ht]
  exact ThinMatrix.GoodMapEmbedding.constructed_raw_embedding L m hm X Y QL QR hgL hgR iL iR aL aR

/-- All high keys are physical stored table addresses. This exact finite
count is independent of cyclic width; complete vectors are stored at
those addresses. Execution and coefficient bit costs remain separate. -/
abbrev HighQueryKeys {L m k : ℕ} (d : SourceQueryData L m k R) (t : ℕ) :=
  Σ ms : ↥(ThinMatrix.OrderedBoxes.orderedBoxMasks t (2*m)).toFinset,
    SelectedAssignments
      (embeddedMask (reindexEmbedding ms.val
        (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape (List.mem_toFinset.mp ms.property)).1
        d.embedding) (reverseMask ms.val))
      (embeddedSupport (reindexEmbedding ms.val
        (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape (List.mem_toFinset.mp ms.property)).1 d.embedding))

omit [Fintype A] [Fintype B] [CommRing R] in
theorem high_query_key_count {L m k : ℕ} (d : SourceQueryData L m k R) (t : ℕ) :
    Fintype.card (HighQueryKeys d t) = (2*m).choose t * 4^t := by
  exact physicalQuery_key_count L (2*m) t
    (fun ms => reindexEmbedding ms.val
      (ThinMatrix.OrderedBoxes.orderedBoxMasks_shape (List.mem_toFinset.mp ms.property)).1 d.embedding)

/-- Unconditional integer-cyclic decode of the constructed complete finite
query. Arbitrary signed integer inputs and every cyclic target are allowed. -/
theorem constructed_cyclic_decode {q : ℕ} [NeZero q]
    (L m t : ℕ) (hm : m ≤ L) (ht : t ≤ 2*m)
    (X : RawLeftInput L m (L-m) (ThinMatrix.CyclicRing.Cyclic q))
    (Y : RawRightInput L m (L-m) (ThinMatrix.CyclicRing.Cyclic q))
    (QL QR : Finset (Fin L))
    (hgL : QL ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (hgR : QR ∈ ThinMatrix.GoodMapEmbedding.goodSlots L m)
    (iL iR : Cube L) (aL aR : Cube (L-m)) :
    ThinMatrix.CyclicRing.decode L
      ((constructedSourceQuery L m X Y QL QR hgL hgR iL iR aL aR).residual t +
       (constructedSourceQuery L m X Y QL QR hgL hgR iL iR aL aR).high t) =
      ∑ h1, ∑ h2, X QL (outsideBits QL iL) aL h1 h2 * Y QR (outsideBits QR iR) h1 h2 aR := by
  apply ThinMatrix.CyclicRing.decode_residual_plus_boxes
  rw [ThinMatrix.CyclicRing.scale_eq_intCast_mul]
  simpa only [SourceQueryData.numerator, Int.cast_pow, Int.cast_ofNat] using
    constructed_complete_numerator L m t hm ht X Y QL QR hgL hgR iL iR aL aR

end ThinMatrix.CompleteThinProduct

#print axioms ThinMatrix.CompleteThinProduct.constructed_complete_numerator
#print axioms ThinMatrix.CompleteThinProduct.high_query_key_count
#print axioms ThinMatrix.CompleteThinProduct.constructed_cyclic_decode
