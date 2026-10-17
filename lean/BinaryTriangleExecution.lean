import BinaryCell
import AlignedAPSP
import AdaptiveQueryBitBounds
import BinaryControllerExecution
import BinaryAPSPCaller
import BinaryFoldedFactory
import BinaryTriangleSetupCosts

/-!
# Binary execution of the triangle callback

Adaptive inputs remain stored signed bit cells. Runtime arithmetic below
consumes those cells directly. Integer views and the native callback occur
only in refinement statements and erased proof fields. Public finite indices
and resource counters are separate from coefficient arithmetic.
-/

namespace ThinMatrix.BinaryTriangleExecution
open IntegerArithmetic
open BinaryCell

/-- Clear only the stored sign bit; the magnitude list is shared unchanged. -/
def absolute (a : BinaryCell.Cell) : BinaryCell.Cell :=
  ⟨⟨false,a.bits.magnitude⟩,by
    change a.bits.magnitude.length = (value a.bits.magnitude).size
    exact a.canonical.trans (congrArg Nat.size (signedValue_natAbs a.bits))⟩

@[simp] theorem absolute_view (a : BinaryCell.Cell) :
    BinaryCell.view (absolute a) = ((BinaryCell.view a).natAbs : ℤ) := by
  change (value a.bits.magnitude : ℤ) = ((signedValue a.bits).natAbs : ℤ)
  rw [signedValue_natAbs]

@[simp] theorem absolute_magnitude (a : BinaryCell.Cell) :
    (absolute a).bits.magnitude = a.bits.magnitude := rfl

/-- The borrow output of binary magnitude subtraction chooses the larger
stored magnitude. The charge includes the comparison loop and four constant
bit operations for borrow/sign reads, branch selection and the sign write. -/
def maxAbs (a b : BinaryCell.Cell) : FFTBitCost.BinaryResult BinaryCell.Cell :=
  let comparison := subCounted a.bits.magnitude b.bits.magnitude false
  ⟨if comparison.1.2 then absolute b else absolute a, comparison.2+4⟩

 theorem maxAbs_view (a b : BinaryCell.Cell) :
    BinaryCell.view (maxAbs a b).value =
      ((max (BinaryCell.view a).natAbs (BinaryCell.view b).natAbs : ℕ) : ℤ) := by
  have hc := (subCounted_projections a.bits.magnitude b.bits.magnitude false).1
  have hb := subBits_borrow a.bits.magnitude b.bits.magnitude
  have ha : (BinaryCell.view a).natAbs = value a.bits.magnitude :=
    signedValue_natAbs a.bits
  have hb' : (BinaryCell.view b).natAbs = value b.bits.magnitude :=
    signedValue_natAbs b.bits
  simp only [maxAbs]
  split
  next ht =>
    rw [absolute_view]
    have ht' : (subBits a.bits.magnitude b.bits.magnitude false).2 = true := by
      simpa only [hc] using ht
    have hl : (BinaryCell.view a).natAbs < (BinaryCell.view b).natAbs := by
      simpa only [ha,hb'] using hb.mp ht'
    rw [max_eq_right (Nat.le_of_lt hl)]
  next ht =>
    rw [absolute_view]
    have ht' : ¬(subBits a.bits.magnitude b.bits.magnitude false).2 = true := by
      simpa only [hc] using ht
    have hl : (BinaryCell.view b).natAbs ≤ (BinaryCell.view a).natAbs := by
      rw [ha,hb']
      exact Nat.le_of_not_gt (fun h => ht' (hb.mpr h))
    rw [max_eq_left hl]

 theorem maxAbs_size (B : ℕ) (a b : BinaryCell.Cell)
    (ha : (BinaryCell.view a).natAbs.size ≤ B)
    (hb : (BinaryCell.view b).natAbs.size ≤ B) :
    (BinaryCell.view (maxAbs a b).value).natAbs.size ≤ B := by
  simp only [maxAbs]
  split <;> simp only [absolute_view, Int.natAbs_natCast] <;> assumption

 theorem maxAbs_width (B : ℕ) (a b : BinaryCell.Cell)
    (ha : a.bits.magnitude.length ≤ B)
    (hb : b.bits.magnitude.length ≤ B) :
    (maxAbs a b).value.bits.magnitude.length ≤ B := by
  simp only [maxAbs]
  split <;> simp only [absolute_magnitude] <;> assumption

 theorem maxAbs_price (B : ℕ) (a b : BinaryCell.Cell)
    (ha : (BinaryCell.view a).natAbs.size ≤ B)
    (hb : (BinaryCell.view b).natAbs.size ≤ B) :
    (maxAbs a b).bitSteps ≤ 12*B+5 := by
  have hlen : max a.bits.magnitude.length b.bits.magnitude.length ≤ B := by
    rw [BinaryCell.canonical a, BinaryCell.canonical b]
    exact max_le ha hb
  simp only [maxAbs, (subCounted_projections _ _ _).2, columnSteps_eq]
  omega

/-- Canonical magnitudes represent zero exactly by an empty stored list. -/
def isZero (a : BinaryCell.Cell) : Bool := a.bits.magnitude.isEmpty

@[simp] theorem isZero_true (a : BinaryCell.Cell) :
    isZero a = true ↔ BinaryCell.view a = 0 := by
  simp only [isZero, List.isEmpty_iff_length_eq_zero, BinaryCell.canonical,
    Nat.size_eq_zero, Int.natAbs_eq_zero]

abbrev Cell := BinaryCell.Cell
abbrev IntTable (n : ℕ) := StoredMinPlusAPSP.Table n Cell

def viewTable {n : ℕ} (A : IntTable n) : StoredMinPlusAPSP.IntTable n :=
  A.map (fun row => row.map BinaryCell.view)

def read {n : ℕ} (A : IntTable n) (i j : Fin n) : Cell := (A.get i).get j

@[simp] theorem viewTable_read {n : ℕ} (A : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode (viewTable A) i j = BinaryCell.view (read A i j) := by
  simp only [viewTable, StoredMinPlusAPSP.decode, Vector.get_map, read]

def one : Cell := ⟨⟨false,[true]⟩,by decide⟩
def three : Cell := ⟨⟨false,[true,true]⟩,by decide⟩
def negOne : Cell := ⟨⟨true,[true]⟩,by decide⟩

@[simp] theorem one_view : BinaryCell.view one = 1 := rfl
@[simp] theorem three_view : BinaryCell.view three = 3 := rfl
@[simp] theorem negOne_view : BinaryCell.view negOne = -1 := rfl

def window (w : Fin 3) : Cell :=
  if w.val = 0 then negOne else if w.val = 1 then BinaryCell.zero else one

@[simp] theorem window_view (w : Fin 3) :
    BinaryCell.view (window w) = CompleteAPSP.windowValue w := by
  fin_cases w <;> rfl

theorem window_width (w : Fin 3) : (BinaryCell.view (window w)).natAbs.size ≤ 1 := by
  fin_cases w <;> decide

def sumZero (a b t w : Cell) : FFTBitCost.BinaryResult Bool :=
  let ab := BinaryCell.add a b
  let abt := BinaryCell.add ab.value t
  let difference := BinaryCell.sub abt.value w
  ⟨isZero difference.value,ab.bitSteps+abt.bitSteps+difference.bitSteps+1⟩

@[simp] theorem sumZero_true (a b t w : Cell) :
    (sumZero a b t w).value = true ↔
      BinaryCell.view a+BinaryCell.view b+BinaryCell.view t-BinaryCell.view w=0 := by
  simp only [sumZero, isZero_true, BinaryCell.sub_view, BinaryCell.add_view]

theorem add_width (B : ℕ) (a b : Cell)
    (ha : (BinaryCell.view a).natAbs.size ≤ B) (hb : (BinaryCell.view b).natAbs.size ≤ B) :
    (BinaryCell.view (BinaryCell.add a b).value).natAbs.size ≤ B+1 := by
  apply Nat.size_le.mpr
  rw [BinaryCell.add_view, pow_succ]
  have ha' := Nat.size_le.mp ha
  have hb' := Nat.size_le.mp hb
  have hs := Int.natAbs_add_le (BinaryCell.view a) (BinaryCell.view b)
  omega

def scanUnit (B : ℕ) : ℕ := 3000*(B+4)^2

theorem sumZero_price (B : ℕ) (a b t : Cell) (w : Fin 3)
    (ha : (BinaryCell.view a).natAbs.size ≤ B)
    (hb : (BinaryCell.view b).natAbs.size ≤ B)
    (ht : (BinaryCell.view t).natAbs.size ≤ B) :
    (sumZero a b t (window w)).bitSteps ≤ scanUnit B := by
  have hab := add_width B a b ha hb
  have habt := add_width (B+1) (BinaryCell.add a b).value t hab (ht.trans (by omega))
  have h1 := BinaryCell.add_price B a b ha hb
  have h2 := BinaryCell.add_price (B+1) (BinaryCell.add a b).value t hab (ht.trans (by omega))
  have h3 := BinaryCell.sub_price (B+2) (BinaryCell.add (BinaryCell.add a b).value t).value
    (window w) (by simpa only [Nat.add_assoc] using habt) ((window_width w).trans (by omega))
  change (BinaryCell.add a b).bitSteps+
    (BinaryCell.add (BinaryCell.add a b).value t).bitSteps+
    (BinaryCell.sub (BinaryCell.add (BinaryCell.add a b).value t).value (window w)).bitSteps+1 ≤ _
  unfold scanUnit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at *
  nlinarith

structure SlotResult where
  value : Bool
  bitSteps : ℕ
  controlSites : ℕ

def slotTest {n h : ℕ} (A B T : IntTable n) (x : EndToEndAPSP.Incidence n h) (s : Fin h) : SlotResult :=
  if hs : CompactBlocks.index x.2.1 s < n then
    let k : Fin n := ⟨CompactBlocks.index x.2.1 s,hs⟩
    let tested := sumZero (read A x.1.1 k) (read B k x.1.2) (read T x.1.1 x.1.2) (window x.2.2)
    ⟨tested.value,tested.bitSteps,12⟩
  else ⟨false,0,6⟩

theorem slotTest_value {n h : ℕ} (A B T : IntTable n)
    (x : EndToEndAPSP.Incidence n h) (s : Fin h) :
    (slotTest A B T x s).value = EndToEndAPSP.slotTest (viewTable A) (viewTable B) (viewTable T) x s := by
  unfold slotTest EndToEndAPSP.slotTest
  split_ifs with hs
  · apply Bool.eq_iff_iff.mpr
    simp only [sumZero_true, window_view, decide_eq_true_eq, CompactBlocks.localLeft,
      CompactBlocks.localRight, hs, dif_pos, viewTable_read, sub_eq_zero]
  · rfl

def InputBits {n : ℕ} (A B T : IntTable n) (Bnd : ℕ) : Prop :=
  (∀ i k, (BinaryCell.view (read A i k)).natAbs.size ≤ Bnd) ∧
  (∀ k j, (BinaryCell.view (read B k j)).natAbs.size ≤ Bnd) ∧
  (∀ i j, (BinaryCell.view (read T i j)).natAbs.size ≤ Bnd)

/-- A joint value/counter recursion; each stored comparison child is evaluated once. -/
def maxList : List Cell → FFTBitCost.BinaryResult Cell
  | [] => ⟨BinaryCell.zero,0⟩
  | a :: as =>
    let tail := maxList as
    let head := maxAbs a tail.value
    ⟨head.value,head.bitSteps+tail.bitSteps⟩

 theorem maxList_view (xs : List Cell) :
    BinaryCell.view (maxList xs).value =
      (((xs.map (fun a => (BinaryCell.view a).natAbs)).foldr max 0 : ℕ) : ℤ) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [maxList, maxAbs_view, ih, Int.natAbs_natCast,
      List.map_cons, List.foldr_cons]

 theorem maxList_view_natAbs (xs : List Cell) :
    BinaryCell.view (maxList xs).value =
      ((BinaryCell.view (maxList xs).value).natAbs : ℤ) := by
  rw [maxList_view,Int.natAbs_natCast]

 theorem maxList_size (B : ℕ) (xs : List Cell)
    (hx : ∀ x ∈ xs, (BinaryCell.view x).natAbs.size ≤ B) :
    (BinaryCell.view (maxList xs).value).natAbs.size ≤ B := by
  induction xs with
  | nil => simp only [maxList, BinaryCell.zero_view, Int.natAbs_zero, Nat.size_zero]; omega
  | cons a as ih =>
    exact maxAbs_size B a (maxList as).value
      (hx a (List.mem_cons_self))
      (ih (fun x hx' => hx x (List.mem_cons_of_mem a hx')))

 theorem maxList_price (B : ℕ) (xs : List Cell)
    (hx : ∀ x ∈ xs, (BinaryCell.view x).natAbs.size ≤ B) :
    (maxList xs).bitSteps ≤ xs.length*(12*B+5) := by
  induction xs with
  | nil => simp [maxList]
  | cons a as ih =>
    have htail : ∀ x ∈ as, (BinaryCell.view x).natAbs.size ≤ B :=
      fun x hx' => hx x (List.mem_cons_of_mem a hx')
    have ht := ih htail
    have hh := maxAbs_price B a (maxList as).value
      (hx a (List.mem_cons_self)) (maxList_size B as htail)
    change (maxAbs a (maxList as).value).bitSteps+(maxList as).bitSteps ≤ _
    simp only [List.length_cons]
    nlinarith

 theorem maxList_width (B : ℕ) (xs : List Cell)
    (hx : ∀ x ∈ xs, x.bits.magnitude.length ≤ B) :
    (maxList xs).value.bits.magnitude.length ≤ B := by
  rw [BinaryCell.canonical]
  apply maxList_size B xs
  intro x hmem
  simpa only [BinaryCell.canonical] using hx x hmem

 theorem maxList_width_price (B : ℕ) (xs : List Cell)
    (hx : ∀ x ∈ xs, x.bits.magnitude.length ≤ B) :
    (maxList xs).bitSteps ≤ xs.length*(12*B+5) := by
  apply maxList_price B xs
  intro x hmem
  simpa only [BinaryCell.canonical] using hx x hmem

 theorem maxList_upper (xs : List Cell) (W : ℕ)
    (hx : ∀ x ∈ xs, (BinaryCell.view x).natAbs ≤ W) :
    (BinaryCell.view (maxList xs).value).natAbs ≤ W := by
  induction xs with
  | nil => simp [maxList]
  | cons a as ih =>
    simp only [maxList,maxAbs_view,Int.natAbs_natCast]
    exact max_le (hx a List.mem_cons_self)
      (ih (fun x hx' => hx x (List.mem_cons_of_mem a hx')))

 theorem maxList_dominates (xs : List Cell) (x : Cell) (hx : x ∈ xs) :
    (BinaryCell.view x).natAbs ≤ (BinaryCell.view (maxList xs).value).natAbs := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    simp only [maxList,maxAbs_view,Int.natAbs_natCast]
    rcases List.mem_cons.mp hx with h | h
    · subst x; exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

def entries {n : ℕ} (A B T : IntTable n) : List Cell :=
  (List.finRange (n*n)).flatMap (fun p =>
    let ij : Fin n × Fin n := finProdFinEquiv.symm p
    [read A ij.1 ij.2, read B ij.1 ij.2, read T ij.1 ij.2])

theorem mem_entries {n : ℕ} (A B T : IntTable n) (x : Cell) :
    x ∈ entries A B T ↔ ∃ i j, x = read A i j ∨ x = read B i j ∨ x = read T i j := by
  constructor
  · intro h
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp h
    refine ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, ?_⟩
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx
  · rintro ⟨i,j,hx⟩
    apply List.mem_flatMap.mpr
    refine ⟨finProdFinEquiv (i,j), List.mem_finRange _, ?_⟩
    simpa only [Equiv.symm_apply_apply, List.mem_cons, List.not_mem_nil, or_false] using hx

theorem length_entries {n : ℕ} (A B T : IntTable n) :
    (entries A B T).length = 3*n^2 := by
  simp [entries, List.length_flatMap, List.sum_replicate, pow_two, Nat.mul_comm]

/-- One stored-bit maximum scan of the three input tables. -/
def entryMax {n : ℕ} (A B T : IntTable n) : FFTBitCost.BinaryResult Cell :=
  maxList (entries A B T)

 theorem entryMax_view {n : ℕ} (A B T : IntTable n) :
    BinaryCell.view (entryMax A B T).value =
      ((CountedEndToEndAPSP.entryMagnitude (viewTable A) (viewTable B) (viewTable T) : ℕ) : ℤ) := by
  have hn : (BinaryCell.view (maxList (entries A B T)).value).natAbs =
      CountedEndToEndAPSP.entryMagnitude (viewTable A) (viewTable B) (viewTable T) := by
    apply le_antisymm
    · apply maxList_upper
      intro x hx
      rcases (mem_entries A B T x).mp hx with ⟨i,j,hx | hx | hx⟩
      · subst x
        simpa only [viewTable_read] using
          (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).1
      · subst x
        simpa only [viewTable_read] using
          (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).2.1
      · subst x
        simpa only [viewTable_read] using
          (CountedEndToEndAPSP.entryMagnitude_bounds (viewTable A) (viewTable B) (viewTable T) i j).2.2
    · unfold CountedEndToEndAPSP.entryMagnitude
      apply max_le
      · apply Finset.sup_le
        intro p _
        simpa only [viewTable_read] using maxList_dominates (entries A B T) (read A p.1 p.2)
          ((mem_entries A B T _).mpr ⟨p.1,p.2,Or.inl rfl⟩)
      · apply max_le
        · apply Finset.sup_le
          intro p _
          simpa only [viewTable_read] using maxList_dominates (entries A B T) (read B p.1 p.2)
            ((mem_entries A B T _).mpr ⟨p.1,p.2,Or.inr (Or.inl rfl)⟩)
        · apply Finset.sup_le
          intro p _
          simpa only [viewTable_read] using maxList_dominates (entries A B T) (read T p.1 p.2)
            ((mem_entries A B T _).mpr ⟨p.1,p.2,Or.inr (Or.inr rfl)⟩)
  exact (maxList_view_natAbs (entries A B T)).trans (congrArg (fun v : ℕ => (v : ℤ)) hn)

 theorem entries_size {n Bnd : ℕ} (A B T : IntTable n) (hx : InputBits A B T Bnd) :
    ∀ x ∈ entries A B T, (BinaryCell.view x).natAbs.size ≤ Bnd := by
  intro x hmem
  rcases (mem_entries A B T x).mp hmem with ⟨i,j,hx' | hx' | hx'⟩
  · subst x; exact hx.1 i j
  · subst x; exact hx.2.1 i j
  · subst x; exact hx.2.2 i j

 theorem entryMax_size {n Bnd : ℕ} (A B T : IntTable n) (hx : InputBits A B T Bnd) :
    (BinaryCell.view (entryMax A B T).value).natAbs.size ≤ Bnd :=
  maxList_size Bnd (entries A B T) (entries_size A B T hx)

 theorem entryMax_price {n Bnd : ℕ} (A B T : IntTable n) (hx : InputBits A B T Bnd) :
    (entryMax A B T).bitSteps ≤ 3*n^2*(12*Bnd+5) := by
  simpa only [entryMax,length_entries] using maxList_price Bnd (entries A B T) (entries_size A B T hx)


/-- Compute the actual cap-test left side from the stored maximum once. -/
def entryBound {n : ℕ} (A B T : IntTable n) : FFTBitCost.BinaryResult Cell :=
  let largest := entryMax A B T
  let triple := BinaryCell.mul three largest.value
  let bound := BinaryCell.add triple.value one
  ⟨bound.value,largest.bitSteps+triple.bitSteps+bound.bitSteps⟩

theorem entryBound_view {n : ℕ} (A B T : IntTable n) :
    BinaryCell.view (entryBound A B T).value =
      (CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) : ℤ) := by
  simp only [entryBound, BinaryCell.add_view, BinaryCell.mul_view, three_view,
    one_view, entryMax_view, CountedEndToEndAPSP.entryQueryBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]

/-- Unsigned borrow compares two nonnegative maintained cells. -/
def atMost (a b : Cell) : FFTBitCost.BinaryResult Bool :=
  let comparison := subCounted b.bits.magnitude a.bits.magnitude false
  ⟨!comparison.1.2,comparison.2+1⟩

theorem atMost_true (a b : Cell) (ha : 0 ≤ BinaryCell.view a) (hb : 0 ≤ BinaryCell.view b) :
    (atMost a b).value = true ↔ BinaryCell.view a ≤ BinaryCell.view b := by
  have hp := (subCounted_projections b.bits.magnitude a.bits.magnitude false).1
  have hborrow := subBits_borrow b.bits.magnitude a.bits.magnitude
  have ha' : BinaryCell.view a = (value a.bits.magnitude : ℤ) := by
    rw [← signedValue_natAbs a.bits]
    rw [Int.natCast_natAbs]
    change BinaryCell.view a = |BinaryCell.view a|
    rw [abs_of_nonneg ha]
  have hb' : BinaryCell.view b = (value b.bits.magnitude : ℤ) := by
    rw [← signedValue_natAbs b.bits]
    rw [Int.natCast_natAbs]
    change BinaryCell.view b = |BinaryCell.view b|
    rw [abs_of_nonneg hb]
  change (!((subCounted b.bits.magnitude a.bits.magnitude false).1.2)) = true ↔ _
  rw [hp]
  have hn : (!(subBits b.bits.magnitude a.bits.magnitude false).2) = true ↔
      ¬(subBits b.bits.magnitude a.bits.magnitude false).2 = true := by
    cases (subBits b.bits.magnitude a.bits.magnitude false).2 <;> decide
  rw [hn,hborrow,ha',hb']
  exact_mod_cast (not_lt : ¬ value b.bits.magnitude < value a.bits.magnitude ↔
    value a.bits.magnitude ≤ value b.bits.magnitude)

theorem atMost_price (Bnd : ℕ) (a b : Cell)
    (ha : (BinaryCell.view a).natAbs.size ≤ Bnd) (hb : (BinaryCell.view b).natAbs.size ≤ Bnd) :
    (atMost a b).bitSteps ≤ 12*Bnd+2 := by
  have hm : max b.bits.magnitude.length a.bits.magnitude.length ≤ Bnd := by
    rw [BinaryCell.canonical,BinaryCell.canonical]
    exact max_le hb ha
  simp only [atMost, (subCounted_projections _ _ _).2,columnSteps_eq]
  omega

theorem mul_three_size (Bnd : ℕ) (a : Cell)
    (ha : (BinaryCell.view a).natAbs.size ≤ Bnd) :
    (BinaryCell.view (BinaryCell.mul three a).value).natAbs.size ≤ Bnd+2 := by
  apply Nat.size_le.mpr
  have ha' := Nat.size_le.mp ha
  rw [BinaryCell.mul_view, Int.natAbs_mul, three_view]
  norm_num only
  rw [show Bnd+2=Bnd+1+1 by omega,pow_succ,pow_succ]
  have hp : 0 < 2^Bnd := pow_pos (by decide) _
  omega

 theorem entryBound_size {n Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) :
    (BinaryCell.view (entryBound A B T).value).natAbs.size ≤ Bnd+3 := by
  have hm := mul_three_size Bnd (entryMax A B T).value (entryMax_size A B T hx)
  have ho : (BinaryCell.view one).natAbs.size ≤ Bnd+2 := by
    norm_num only [one_view,Int.natAbs_one,Nat.size_one]
    omega
  have ha := add_width (Bnd+2) (BinaryCell.mul three (entryMax A B T).value).value one hm ho
  exact ha

 theorem entryBound_price {n Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) :
    (entryBound A B T).bitSteps ≤ 3*n^2*(12*Bnd+5)+
      2*BackendScalarBits.backendScalarUnit (Bnd+3) := by
  have hmax := entryMax_price A B T hx
  have hm := entryMax_size A B T hx
  have htr := mul_three_size Bnd (entryMax A B T).value hm
  have hthree : (BinaryCell.view three).natAbs.size ≤ Bnd+3 := by
    have hsize : (BinaryCell.view three).natAbs.size = 2 := by decide
    omega
  have hone : (BinaryCell.view one).natAbs.size ≤ Bnd+3 := by
    norm_num only [one_view,Int.natAbs_one,Nat.size_one]
    omega
  have hmul := BinaryCell.mul_price (Bnd+3) three (entryMax A B T).value hthree (hm.trans (by omega))
  have hadd := BinaryCell.add_price (Bnd+3) (BinaryCell.mul three (entryMax A B T).value).value
    one (htr.trans (by omega)) hone
  change (entryMax A B T).bitSteps+(BinaryCell.mul three (entryMax A B T).value).bitSteps+
    (BinaryCell.add (BinaryCell.mul three (entryMax A B T).value).value one).bitSteps ≤ _
  omega

 theorem entryBound_price_explicit {n Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) :
    (entryBound A B T).bitSteps ≤ 3*n^2*(12*Bnd+5)+3000*(Bnd+5)^2 := by
  have hp := entryBound_price A B T hx
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at hp
  nlinarith

 theorem entryBound_atMost_price {n Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) (cap : Cell)
    (hcap : (BinaryCell.view cap).natAbs.size ≤ Bnd+3) :
    (atMost (entryBound A B T).value cap).bitSteps ≤ 12*(Bnd+3)+2 :=
  atMost_price (Bnd+3) _ cap (entryBound_size A B T hx) hcap

theorem slotTest_price {n h Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) (x : EndToEndAPSP.Incidence n h) (s : Fin h) :
    (slotTest A B T x s).bitSteps ≤ scanUnit Bnd ∧ (slotTest A B T x s).controlSites ≤ 12 := by
  unfold slotTest
  split_ifs with hs
  · exact ⟨sumZero_price Bnd _ _ _ _ (hx.1 _ _) (hx.2.1 _ _) (hx.2.2 _ _),le_rfl⟩
  · exact ⟨Nat.zero_le _,by decide⟩

structure Scan where
  yes : Bool
  tests : ℕ
  bitSteps : ℕ
  controlSites : ℕ

def scanSlots {n h : ℕ} (A B T : IntTable n) (x : EndToEndAPSP.Incidence n h) :
    List (Fin h) → Scan
  | [] => ⟨false,0,0,1⟩
  | s :: ss =>
    let head := slotTest A B T x s
    let tail := scanSlots A B T x ss
    ⟨head.value || tail.yes,tail.tests+1,head.bitSteps+tail.bitSteps,
      head.controlSites+tail.controlSites+3⟩

theorem scanSlots_value {n h : ℕ} (A B T : IntTable n)
    (x : EndToEndAPSP.Incidence n h) (ss : List (Fin h)) :
    ((scanSlots A B T x ss).yes,(scanSlots A B T x ss).tests) =
      EndToEndAPSP.scanBool (EndToEndAPSP.slotTest (viewTable A) (viewTable B) (viewTable T) x) ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hy := congrArg Prod.fst ih
    have ht := congrArg Prod.snd ih
    dsimp only at hy ht
    simp only [scanSlots, EndToEndAPSP.scanBool, slotTest_value, hy, ht]

theorem scanSlots_tests {n h : ℕ} (A B T : IntTable n)
    (x : EndToEndAPSP.Incidence n h) (ss : List (Fin h)) :
    (scanSlots A B T x ss).tests = ss.length := by
  have h := congrArg Prod.snd (scanSlots_value A B T x ss)
  exact h.trans (EndToEndAPSP.scanBool_tests _ _)

theorem scanSlots_price {n h Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd) (x : EndToEndAPSP.Incidence n h) (ss : List (Fin h)) :
    (scanSlots A B T x ss).bitSteps ≤ ss.length*scanUnit Bnd ∧
      (scanSlots A B T x ss).controlSites ≤ 15*ss.length+1 := by
  induction ss with
  | nil => exact ⟨Nat.zero_le _,le_rfl⟩
  | cons s ss ih =>
    have hh := slotTest_price A B T hx x s
    simp only [scanSlots, List.length_cons]
    constructor <;> nlinarith [hh.1,hh.2,ih.1,ih.2]

/-- Binary fallback: stored operands are added and tested without integer reencoding. -/
def directScan {n : ℕ} (A B T : IntTable n) (i j : Fin n) : List (Fin n) → Scan
  | [] => ⟨false,0,0,1⟩
  | k :: ks =>
    let head := sumZero (read A i k) (read B k j) (read T i j) BinaryCell.zero
    let tail := directScan A B T i j ks
    ⟨head.value || tail.yes,tail.tests+1,head.bitSteps+tail.bitSteps,
      tail.controlSites+9⟩

theorem directScan_value {n : ℕ} (A B T : IntTable n) (i j : Fin n) (ks : List (Fin n)) :
    ((directScan A B T i j ks).yes,(directScan A B T i j ks).tests) =
      EndToEndAPSP.directScan (viewTable A) (viewTable B) (viewTable T) i j ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hz : (sumZero (read A i k) (read B k j) (read T i j) BinaryCell.zero).value =
        decide (StoredMinPlusAPSP.decode (viewTable A) i k+
          StoredMinPlusAPSP.decode (viewTable B) k j+
          StoredMinPlusAPSP.decode (viewTable T) i j=0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [sumZero_true, BinaryCell.zero_view, sub_zero, viewTable_read, decide_eq_true_eq]
    have hy := congrArg Prod.fst ih
    have ht := congrArg Prod.snd ih
    dsimp only at hy ht
    simp only [directScan, EndToEndAPSP.directScan, hz, hy, ht]

theorem directScan_price {n Bnd : ℕ} (A B T : IntTable n) (hx : InputBits A B T Bnd)
    (i j : Fin n) (ks : List (Fin n)) :
    (directScan A B T i j ks).bitSteps ≤ ks.length*scanUnit Bnd ∧
    (directScan A B T i j ks).controlSites ≤ 9*ks.length+1 := by
  induction ks with
  | nil => exact ⟨Nat.zero_le _,le_rfl⟩
  | cons k ks ih =>
    have hh := sumZero_price Bnd (read A i k) (read B k j) (read T i j) ⟨1,by decide⟩
      (hx.1 i k) (hx.2.1 k j) (hx.2.2 i j)
    have hz : window ⟨1,by decide⟩ = BinaryCell.zero := rfl
    rw [hz] at hh
    simp only [directScan, List.length_cons]
    constructor <;> nlinarith [ih.1,ih.2]

structure DirectPayload (n : ℕ) where
  scans : StoredMinPlusAPSP.Table n Scan
  tests : ℕ
  bitSteps : ℕ
  controlSites : ℕ

def directOracle (n : ℕ) : IntTable n → IntTable n → IntTable n →
    StoredMinPlusAPSP.OracleOutput n (DirectPayload n) := fun A B T =>
  let scans := StoredMinPlusAPSP.store (fun i j => directScan A B T i j (List.finRange n))
  let tests := ∑ i : Fin n, ∑ j : Fin n, (StoredMinPlusAPSP.decode scans i j).tests
  let bits := ∑ i : Fin n, ∑ j : Fin n, (StoredMinPlusAPSP.decode scans i j).bitSteps
  let sites := ∑ i : Fin n, ∑ j : Fin n, (StoredMinPlusAPSP.decode scans i j).controlSites
  { answers := StoredMinPlusAPSP.store (fun i j => (StoredMinPlusAPSP.decode scans i j).yes)
    payload := ⟨scans,tests,bits,sites+2*n*n⟩
    work := bits+sites+2*n*n
    answerWrites := n*n }

theorem directOracle_answers (n : ℕ) (A B T : IntTable n) :
    (directOracle n A B T).answers =
      (EndToEndAPSP.directCallback n (viewTable A) (viewTable B) (viewTable T)).answers := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hv := congrArg Prod.fst (directScan_value A B T ⟨i,hi⟩ ⟨j,hj⟩ (List.finRange n))
  simpa only [directOracle, EndToEndAPSP.directCallback, StoredMinPlusAPSP.store,
    StoredMinPlusAPSP.decode, Vector.getElem_ofFn, Vector.get_ofFn] using hv

theorem directOracle_correct (n : ℕ) (A B T : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode (directOracle n A B T).answers i j = true ↔
      ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+
        BinaryCell.view (read T i j)=0 := by
  rw [directOracle_answers]
  simpa only [viewTable_read] using EndToEndAPSP.directCallback_correct n
    (viewTable A) (viewTable B) (viewTable T) i j

theorem directOracle_tests (n : ℕ) (A B T : IntTable n) :
    (directOracle n A B T).payload.tests = n^3 := by
  have he : ∀ i j, (directScan A B T i j (List.finRange n)).tests = n := by
    intro i j
    have hv := congrArg Prod.snd (directScan_value A B T i j (List.finRange n))
    exact hv.trans (by simp only [EndToEndAPSP.directScan_tests, List.length_finRange])
  simp only [directOracle, StoredMinPlusAPSP.decode_store, he]
  simp [pow_succ, Nat.mul_assoc]

/-- Each surviving compact incidence is scanned once and its return is retained. -/
def finalScans {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    Vector Scan (EndToEndAPSP.incidenceSize n h) :=
  Vector.ofFn (fun i => if active.get i then
    scanSlots A B T ((EndToEndAPSP.incidenceEquiv n h).symm i) (List.finRange h)
    else ⟨false,0,0,1⟩)

def projectScans {I : ℕ} (ss : Vector Scan I) : Vector (Bool × ℕ) I :=
  ss.map (fun s => (s.yes,s.tests))

theorem finalScans_project {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    projectScans (finalScans A B T active) =
      EndToEndAPSP.finalScans (viewTable A) (viewTable B) (viewTable T) active := by
  apply Vector.ext
  intro i hi
  simp only [projectScans, Vector.getElem_map, finalScans, EndToEndAPSP.finalScans,
    Vector.getElem_ofFn]
  split_ifs with ha
  · exact scanSlots_value A B T _ _
  · rfl

theorem finalScans_tests {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    (∑ i : Fin (EndToEndAPSP.incidenceSize n h), ((finalScans A B T active).get i).tests) =
      h*(ArrayCompositeAlgorithm.decode active).card := by
  have he := EndToEndAPSP.scanTests_eq (viewTable A) (viewTable B) (viewTable T) active
  rw [← finalScans_project] at he
  simpa only [EndToEndAPSP.scanTests,projectScans,Vector.get_map] using he

theorem directOracle_price {Bnd : ℕ} (n : ℕ) (A B T : IntTable n)
    (hx : InputBits A B T Bnd) :
    (directOracle n A B T).payload.bitSteps ≤ n^3*scanUnit Bnd ∧
      (directOracle n A B T).payload.controlSites ≤ 9*n^3+3*n^2 := by
  have hb : ∀ i j : Fin n,
      (directScan A B T i j (List.finRange n)).bitSteps ≤ n*scanUnit Bnd := by
    intro i j
    simpa only [List.length_finRange] using (directScan_price A B T hx i j (List.finRange n)).1
  have hc : ∀ i j : Fin n,
      (directScan A B T i j (List.finRange n)).controlSites ≤ 9*n+1 := by
    intro i j
    simpa only [List.length_finRange] using (directScan_price A B T hx i j (List.finRange n)).2
  simp only [directOracle, StoredMinPlusAPSP.decode_store]
  constructor
  · calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, n*scanUnit Bnd :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = n^3*scanUnit Bnd := by simp; ring
  · calc
      _ ≤ (∑ _i : Fin n, ∑ _j : Fin n, (9*n+1))+2*n*n := by
        apply Nat.add_le_add_right
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hc i j))
      _ = 9*n^3+3*n^2 := by simp; ring

theorem finalScans_price {n h Bnd : ℕ} (A B T : IntTable n)
    (hx : InputBits A B T Bnd)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    (∑ i : Fin (EndToEndAPSP.incidenceSize n h),
      ((finalScans A B T active).get i).bitSteps) ≤
        scanUnit Bnd * (∑ i : Fin (EndToEndAPSP.incidenceSize n h),
          ((finalScans A B T active).get i).tests) ∧
    (∑ i : Fin (EndToEndAPSP.incidenceSize n h),
      ((finalScans A B T active).get i).controlSites) ≤
        15*(∑ i : Fin (EndToEndAPSP.incidenceSize n h),
          ((finalScans A B T active).get i).tests)+EndToEndAPSP.incidenceSize n h := by
  have hp : ∀ i : Fin (EndToEndAPSP.incidenceSize n h),
      ((finalScans A B T active).get i).bitSteps ≤
        scanUnit Bnd * ((finalScans A B T active).get i).tests ∧
      ((finalScans A B T active).get i).controlSites ≤
        15*((finalScans A B T active).get i).tests+1 := by
    intro i
    simp only [finalScans, Vector.get_ofFn]
    split_ifs with ha
    · have hi := scanSlots_price A B T hx
        ((EndToEndAPSP.incidenceEquiv n h).symm i) (List.finRange h)
      constructor
      · simpa only [scanSlots_tests,Nat.mul_comm] using hi.1
      · simpa only [scanSlots_tests] using hi.2
    · exact ⟨by simp,by simp⟩
  constructor
  · calc
      _ ≤ ∑ i : Fin (EndToEndAPSP.incidenceSize n h),
          scanUnit Bnd * ((finalScans A B T active).get i).tests :=
        Finset.sum_le_sum (fun i _ => (hp i).1)
      _ = _ := by rw [Finset.mul_sum]
  · calc
      _ ≤ ∑ i : Fin (EndToEndAPSP.incidenceSize n h),
          (15*((finalScans A B T active).get i).tests+1) :=
        Finset.sum_le_sum (fun i _ => (hp i).2)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp

def scanAnswers {I : ℕ} (ss : Vector Scan I) : ArrayCompositeAlgorithm.Flags I :=
  ss.map Scan.yes

theorem scanAnswers_project {n h : ℕ} (ss : Vector Scan (EndToEndAPSP.incidenceSize n h)) :
    scanAnswers ss = EndToEndAPSP.scanAnswers (projectScans ss) := by
  apply Vector.ext
  intro i hi
  simp only [scanAnswers,projectScans,EndToEndAPSP.scanAnswers,Vector.getElem_map,
    Vector.getElem_ofFn,Vector.get_map]
  rfl

structure Finished (n h : ℕ) (Call : Type) where
  answers : StoredMinPlusAPSP.BoolTable n
  scans : Vector Scan (EndToEndAPSP.incidenceSize n h)
  marked : ArrayCompositeAlgorithm.Flags (n*n)
  calls : List Call
  backendWork : ℕ
  bitSteps : ℕ
  controlSites : ℕ
  originalSumTests : ℕ
  finalScatterWrites : ℕ
  denseAnswerWrites : ℕ

/-- Finalization consumes the retained controller fields. It cannot invoke a producer. -/
def finalize {n h : ℕ} {Call : Type}
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites : ℕ) (A B T : IntTable n) : Finished n h Call :=
  let scans := finalScans A B T active
  let yes := scanAnswers scans
  let scattered := CountedEndToEndAPSP.scatter (EndToEndAPSP.ownerTable n h) yes marked
    (List.finRange (EndToEndAPSP.incidenceSize n h))
  { answers := StoredMinPlusAPSP.store (fun i j => scattered.flags.get (finProdFinEquiv (i,j)))
    scans := scans
    marked := scattered.flags
    calls := calls
    backendWork := backendWork
    bitSteps := controllerBits+∑ i : Fin (EndToEndAPSP.incidenceSize n h), (scans.get i).bitSteps
    controlSites := controllerSites+
      (∑ i : Fin (EndToEndAPSP.incidenceSize n h), (scans.get i).controlSites)+
      2*EndToEndAPSP.incidenceSize n h+scattered.visits+n*n
    originalSumTests := ∑ i : Fin (EndToEndAPSP.incidenceSize n h), (scans.get i).tests
    finalScatterWrites := scattered.writes
    denseAnswerWrites := n*n }

theorem finalize_answers {n h P : ℕ} {Payload : Type}
    (controller : CountedArrayComposite.StageResult P (EndToEndAPSP.incidenceSize n h) (n*n) Payload)
    (controllerBits controllerSites : ℕ) (A B T : IntTable n) :
    (finalize controller.active controller.marked controller.calls controller.backendWork
      controllerBits controllerSites A B T).answers =
    (CountedEndToEndAPSP.finalize controller (viewTable A) (viewTable B) (viewTable T)).answers := by
  simp only [finalize, CountedEndToEndAPSP.finalize, ← finalScans_project,
    ← scanAnswers_project]

theorem finalize_tests {n h P : ℕ} {Payload : Type}
    (controller : CountedArrayComposite.StageResult P (EndToEndAPSP.incidenceSize n h) (n*n) Payload)
    (controllerBits controllerSites : ℕ) (A B T : IntTable n) :
    (finalize controller.active controller.marked controller.calls controller.backendWork
      controllerBits controllerSites A B T).originalSumTests =
    (CountedEndToEndAPSP.finalize controller (viewTable A) (viewTable B) (viewTable T)).resources.originalSumTests := by
  simp only [finalize, CountedEndToEndAPSP.finalize, ← finalScans_project,
    EndToEndAPSP.scanTests, projectScans,Vector.get_map]

theorem finalize_price {n h Bnd : ℕ} {Call : Type}
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites : ℕ) (A B T : IntTable n)
    (hx : InputBits A B T Bnd) :
    let out := finalize active marked calls backendWork controllerBits controllerSites A B T
    out.bitSteps ≤ controllerBits+scanUnit Bnd*out.originalSumTests ∧
    out.controlSites ≤ controllerSites+15*out.originalSumTests+
      4*EndToEndAPSP.incidenceSize n h+n*n := by
  have hs := finalScans_price A B T hx active
  have hv := CountedEndToEndAPSP.scatter_visits (EndToEndAPSP.ownerTable n h)
    (scanAnswers (finalScans A B T active)) marked
    (List.finRange (EndToEndAPSP.incidenceSize n h))
  simp only [List.length_finRange] at hv
  simp only [finalize]
  rw [hv]
  constructor <;> omega

theorem finalize_answers_mark {n h : ℕ} {Call : Type}
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites : ℕ) (A B T : IntTable n) :
    (finalize active marked calls backendWork controllerBits controllerSites A B T).answers =
      StoredMinPlusAPSP.store (fun i j =>
        (ArrayCompositeAlgorithm.mark (EndToEndAPSP.ownerTable n h)
          (EndToEndAPSP.scanAnswers (EndToEndAPSP.finalScans (viewTable A) (viewTable B)
            (viewTable T) active)) marked).get (finProdFinEquiv (i,j))) := by
  simp only [finalize,CountedEndToEndAPSP.scatter_value,ArrayCompositeAlgorithm.mark,
    ← finalScans_project, ← scanAnswers_project]

theorem finalize_correct_of_invariant {n h : ℕ} {Call : Type} (hh : 0 < h)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites : ℕ) (A B T : IntTable n)
    (hinv : (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).StateInvariant
      (EndToEndAPSP.ownerTable n h).get
      (ArrayCompositeAlgorithm.decode (EndToEndAPSP.initialFlags n h))
      (ArrayCompositeAlgorithm.decode active) (ArrayCompositeAlgorithm.decode marked)) (i j : Fin n) :
    StoredMinPlusAPSP.decode
      (finalize active marked calls backendWork controllerBits controllerSites A B T).answers i j = true ↔
      ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+BinaryCell.view (read T i j)=0 := by
  have hm := EndToEndAPSP.finalScans_mark_correct hh (viewTable A) (viewTable B) (viewTable T) active marked
  have hf := ArrayCompositeAlgorithm.final_scan_of_invariant
    (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T))
    (EndToEndAPSP.ownerTable n h) (ArrayCompositeAlgorithm.decode (EndToEndAPSP.initialFlags n h))
    active marked hinv
  have hmem := Finset.ext_iff.mp (hm.trans hf) (finProdFinEquiv (i,j))
  rw [finalize_answers_mark]
  simpa only [StoredMinPlusAPSP.decode_store, ArrayCompositeAlgorithm.mem_decode, viewTable_read] using
    hmem.trans (EndToEndAPSP.initial_exactPairs_zero hh (viewTable A) (viewTable B) (viewTable T) i j)

theorem finalize_scan_budget {n h stages : ℕ} {Call : Type} (hhn : h ≤ n)
    (hs : (2*n).size ≤ stages)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (marked : ArrayCompositeAlgorithm.Flags (n*n)) (calls : List Call)
    (backendWork controllerBits controllerSites : ℕ) (A B T : IntTable n)
    (hhalf : 2^stages*(ArrayCompositeAlgorithm.decode active).card ≤
      n^2*CompactBlocks.blockCount n h) :
    (finalize active marked calls backendWork controllerBits controllerSites A B T).originalSumTests ≤ n^2 := by
  change (∑ i,((finalScans A B T active).get i).tests) ≤ _
  rw [finalScans_tests]
  have hb := CompactStoredAPSP.scan_budget hhn hs
  apply Nat.le_of_mul_le_mul_left (c:=2^stages) ?_ (by positivity)
  calc
    _ = h*(2^stages*(ArrayCompositeAlgorithm.decode active).card) := by ring
    _ ≤ h*(n^2*CompactBlocks.blockCount n h) := Nat.mul_le_mul_left h hhalf
    _ = h*n^2*CompactBlocks.blockCount n h := by ring
    _ ≤ _ := hb

/-- Public prime labels are materialized once into maintained binary cells. -/
def prepareStaticPrimes {P : ℕ} (labels : Vector ℕ P) :
    BinaryControllerExecution.Result (BinaryControllerExecution.Primes P) :=
  BinaryControllerExecution.tabulate (fun i => BinaryControllerExecution.preparePrime (labels.get i))

 theorem prepareStaticPrimes_project {P : ℕ} (labels : Vector ℕ P) :
    BinaryControllerExecution.projectPrimes (prepareStaticPrimes labels).value = labels := by
  rw [prepareStaticPrimes,BinaryControllerExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [BinaryControllerExecution.projectPrimes,Vector.getElem_map,Vector.getElem_ofFn,
    BinaryControllerExecution.preparePrime]
  rfl

/-- Public block sizes are materialized once; adaptive coefficient values
never pass through this public binary-recursion interface. -/
def prepareStaticCounts {I : ℕ} (counts : Vector ℕ I) :
    BinaryControllerExecution.Result (BinaryControllerExecution.Counts I) :=
  BinaryControllerExecution.tabulate (fun i => BinaryControllerExecution.fromPublic (counts.get i))

 theorem prepareStaticCounts_project {I : ℕ} (counts : Vector ℕ I) :
    BinaryControllerExecution.projectCounts (prepareStaticCounts counts).value = counts := by
  rw [prepareStaticCounts,BinaryControllerExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [BinaryControllerExecution.projectCounts,Vector.getElem_map,Vector.getElem_ofFn,
    BinaryControllerExecution.fromPublic_nview]
  rfl

/-- Retained setup data for a fixed public composite-controller shape. -/
structure Static {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) where
  primes : BinaryControllerExecution.Primes parameters.pool.card
  blockSizes : BinaryControllerExecution.Counts (EndToEndAPSP.incidenceSize n h)
  lam : BinaryControllerExecution.NatCell
  cap : BinaryControllerExecution.NatCell
  primes_eq : BinaryControllerExecution.projectPrimes primes = EndToEndAPSP.primeVector parameters.pool
  blockSizes_eq : BinaryControllerExecution.projectCounts blockSizes = EndToEndAPSP.blockSizeTable n h
  lam_eq : BinaryControllerExecution.nview lam = parameters.lam
  cap_eq : BinaryControllerExecution.nview cap = U

/-- One public setup, retaining each joint producer result before extracting
its stored values and ghost counters. -/
def setupStatic {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    BinaryControllerExecution.Result (Static (n := n) parameters) :=
  let publicPrimes := EndToEndAPSP.primeVector parameters.pool
  let publicSizes := EndToEndAPSP.blockSizeTable n h
  let primes := prepareStaticPrimes publicPrimes
  let sizes := prepareStaticCounts publicSizes
  let lam := BinaryControllerExecution.fromPublic parameters.lam
  let cap := BinaryControllerExecution.fromPublic U
  ⟨⟨primes.value,sizes.value,lam.value,cap.value,
      prepareStaticPrimes_project publicPrimes,prepareStaticCounts_project publicSizes,
      BinaryControllerExecution.fromPublic_nview parameters.lam,
      BinaryControllerExecution.fromPublic_nview U⟩,
    primes.bitSteps+sizes.bitSteps+lam.bitSteps+cap.bitSteps,
    primes.controlSites+sizes.controlSites+lam.controlSites+cap.controlSites+8,
    primes.arithSites+sizes.arithSites+lam.arithSites+cap.arithSites⟩

 theorem setupStatic_primes {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    BinaryControllerExecution.projectPrimes (setupStatic (n := n) parameters).value.primes =
      EndToEndAPSP.primeVector parameters.pool := (setupStatic parameters).value.primes_eq

 theorem setupStatic_blockSizes {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    BinaryControllerExecution.projectCounts (setupStatic (n := n) parameters).value.blockSizes =
      EndToEndAPSP.blockSizeTable n h := (setupStatic parameters).value.blockSizes_eq

 theorem setupStatic_lam {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    BinaryControllerExecution.nview (setupStatic (n := n) parameters).value.lam = parameters.lam :=
  (setupStatic parameters).value.lam_eq

 theorem setupStatic_cap {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    BinaryControllerExecution.nview (setupStatic (n := n) parameters).value.cap = U :=
  (setupStatic parameters).value.cap_eq


 theorem staticFromPublic_zero (v : ℕ) :
    (BinaryControllerExecution.fromPublic v).bitSteps = 0 ∧
      (BinaryControllerExecution.fromPublic v).arithSites = 0 :=
  BinaryControllerExecution.publicBits_zero_bits v

 theorem prepareStaticPrimes_zero {P : ℕ} (labels : Vector ℕ P) :
    (prepareStaticPrimes labels).bitSteps = 0 ∧ (prepareStaticPrimes labels).arithSites = 0 := by
  constructor
  · apply BinaryControllerExecution.tabulate_zero_bits
    intro i
    exact (staticFromPublic_zero (labels.get i)).1
  · apply BinaryControllerExecution.tabulate_zero_arith
    intro i
    exact (staticFromPublic_zero (labels.get i)).2

 theorem prepareStaticCounts_zero {I : ℕ} (counts : Vector ℕ I) :
    (prepareStaticCounts counts).bitSteps = 0 ∧ (prepareStaticCounts counts).arithSites = 0 := by
  constructor
  · apply BinaryControllerExecution.tabulate_zero_bits
    intro i
    exact (staticFromPublic_zero (counts.get i)).1
  · apply BinaryControllerExecution.tabulate_zero_arith
    intro i
    exact (staticFromPublic_zero (counts.get i)).2

 theorem setupStatic_zero {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    (setupStatic (n := n) parameters).bitSteps = 0 ∧
      (setupStatic (n := n) parameters).arithSites = 0 := by
  simp only [setupStatic, (prepareStaticPrimes_zero _).1, (prepareStaticCounts_zero _).1,
    (prepareStaticPrimes_zero _).2, (prepareStaticCounts_zero _).2,
    (staticFromPublic_zero _).1, (staticFromPublic_zero _).2, zero_add, and_self]

 theorem staticScanTotals_control_eq {N : ℕ} {α : Type*}
    (stored : Vector (BinaryControllerExecution.Result α) N) (is : List (Fin N)) :
    (BinaryControllerExecution.scanTotals stored is).controlSites =
      (is.map (fun i => (stored.get i).controlSites)).sum+6*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [BinaryControllerExecution.scanTotals,ih]; omega

 theorem staticTabulate_control_eq {N : ℕ} {α : Type*}
    (f : Fin N → BinaryControllerExecution.Result α) :
    (BinaryControllerExecution.tabulate f).controlSites =
      (∑ i : Fin N, (f i).controlSites)+13*N+2 := by
  simp only [BinaryControllerExecution.tabulate,staticScanTotals_control_eq,
    Vector.get_ofFn,List.length_finRange]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  omega

 theorem setupStatic_control_eq {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U) :
    (setupStatic (n := n) parameters).controlSites =
      (∑ i : Fin parameters.pool.card,
        (8*((EndToEndAPSP.primeVector parameters.pool).get i).size+5))+
      (∑ i : Fin (EndToEndAPSP.incidenceSize n h),
        (8*((EndToEndAPSP.blockSizeTable n h).get i).size+3))+
      13*(parameters.pool.card+EndToEndAPSP.incidenceSize n h)+
      8*parameters.lam.size+8*U.size+18 := by
  simp only [setupStatic,prepareStaticPrimes,prepareStaticCounts,staticTabulate_control_eq,
    BinaryControllerExecution.preparePrime_control,BinaryControllerExecution.fromPublic_control]
  omega

 theorem prepareStaticPrimes_control {P W : ℕ} (labels : Vector ℕ P)
    (hl : ∀ i, (labels.get i).size ≤ W) :
    (prepareStaticPrimes labels).controlSites ≤ P*(8*W+18)+2 := by
  apply BinaryControllerExecution.tabulate_control_le (C := 8*W+5)
  intro i
  rw [BinaryControllerExecution.preparePrime_control]
  have hi := hl i
  omega

 theorem prepareStaticCounts_control {I W : ℕ} (counts : Vector ℕ I)
    (hc : ∀ i, (counts.get i).size ≤ W) :
    (prepareStaticCounts counts).controlSites ≤ I*(8*W+16)+2 := by
  apply BinaryControllerExecution.tabulate_control_le (C := 8*W+3)
  intro i
  rw [BinaryControllerExecution.fromPublic_control]
  have hi := hc i
  omega

 theorem setupStatic_control {n h U Wp Wc : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (hp : ∀ i, ((EndToEndAPSP.primeVector parameters.pool).get i).size ≤ Wp)
    (hc : ∀ i, ((EndToEndAPSP.blockSizeTable n h).get i).size ≤ Wc) :
    (setupStatic (n := n) parameters).controlSites ≤
      parameters.pool.card*(8*Wp+18)+EndToEndAPSP.incidenceSize n h*(8*Wc+16)+
      8*parameters.lam.size+8*U.size+18 := by
  have hpr := prepareStaticPrimes_control (EndToEndAPSP.primeVector parameters.pool) hp
  have hco := prepareStaticCounts_control (EndToEndAPSP.blockSizeTable n h) hc
  simp only [setupStatic,BinaryControllerExecution.fromPublic_control]
  omega

 theorem setupStatic_control_public {n h U Wp : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (hp : ∀ i, ((EndToEndAPSP.primeVector parameters.pool).get i).size ≤ Wp) :
    (setupStatic (n := n) parameters).controlSites ≤
      parameters.pool.card*(8*Wp+18)+EndToEndAPSP.incidenceSize n h*(8*h.size+16)+
      8*parameters.lam.size+8*U.size+18 := by
  apply setupStatic_control parameters hp
  intro i
  simp only [EndToEndAPSP.blockSizeTable,Vector.get_ofFn]
  apply Nat.size_le_size
  exact min_le_left _ _

/-- Public indexed-table formation. Each entry charges index decoding,
three bounded arithmetic operations for the block size, and its stored write. -/
def formBlockSizes (n h : ℕ) : BinaryControllerExecution.Result
    (ArrayCompositeAlgorithm.Counts (EndToEndAPSP.incidenceSize n h)) :=
  BinaryControllerExecution.tabulate (fun i =>
    ⟨EndToEndAPSP.slotCount ((EndToEndAPSP.incidenceEquiv n h).symm i).2.1,0,32,0⟩)

@[simp] theorem formBlockSizes_value (n h : ℕ) :
    (formBlockSizes n h).value=EndToEndAPSP.blockSizeTable n h := by
  simp only [formBlockSizes,BinaryControllerExecution.tabulate_value,EndToEndAPSP.blockSizeTable]

@[simp] theorem formBlockSizes_control (n h : ℕ) :
    (formBlockSizes n h).controlSites=45*EndToEndAPSP.incidenceSize n h+2 := by
  rw [formBlockSizes,staticTabulate_control_eq]
  simp
  ring

def formOwner (n h : ℕ) : BinaryControllerExecution.Result
    (ArrayCompositeAlgorithm.Owners (EndToEndAPSP.incidenceSize n h) (n*n)) :=
  BinaryControllerExecution.tabulate (fun i =>
    ⟨finProdFinEquiv (((EndToEndAPSP.incidenceEquiv n h).symm i).1),0,32,0⟩)

@[simp] theorem formOwner_value (n h : ℕ) :
    (formOwner n h).value=EndToEndAPSP.ownerTable n h := by
  simp only [formOwner,BinaryControllerExecution.tabulate_value,EndToEndAPSP.ownerTable]

@[simp] theorem formOwner_control (n h : ℕ) :
    (formOwner n h).controlSites=45*EndToEndAPSP.incidenceSize n h+2 := by
  rw [formOwner,staticTabulate_control_eq]
  simp
  ring

def formInitial (n h : ℕ) : BinaryControllerExecution.Result
    (ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :=
  BinaryControllerExecution.tabulate (fun i =>
    ⟨decide (((EndToEndAPSP.incidenceEquiv n h).symm i).2.2=CompleteAPSP.zeroWindow),0,16,0⟩)

@[simp] theorem formInitial_value (n h : ℕ) :
    (formInitial n h).value=EndToEndAPSP.initialFlags n h := by
  simp only [formInitial,BinaryControllerExecution.tabulate_value,EndToEndAPSP.initialFlags]

@[simp] theorem formInitial_control (n h : ℕ) :
    (formInitial n h).controlSites=29*EndToEndAPSP.incidenceSize n h+2 := by
  rw [formInitial,staticTabulate_control_eq]
  simp
  ring

def formFlags (N : ℕ) (b : Bool) : BinaryControllerExecution.Result (ArrayCompositeAlgorithm.Flags N) :=
  BinaryControllerExecution.tabulate (fun _ => ⟨b,0,1,0⟩)

@[simp] theorem formFlags_value (N : ℕ) (b : Bool) :
    (formFlags N b).value=Vector.replicate N b := by
  simp only [formFlags,BinaryControllerExecution.tabulate_value]
  apply Vector.ext
  intro i hi
  simp

@[simp] theorem formFlags_control (N : ℕ) (b : Bool) :
    (formFlags N b).controlSites=14*N+2 := by
  rw [formFlags,staticTabulate_control_eq]
  simp
  ring

/-- Retained sorted prime labels come from the parameter execution. The erased
 equality removes any need for a second sort or prime-pool enumeration. -/
def setupStaticFromPrimes {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) :
    BinaryControllerExecution.Result (Static (n:=n) parameters) :=
  let publicSizes := formBlockSizes n h
  let primes := prepareStaticPrimes labels
  let sizes := prepareStaticCounts publicSizes.value
  let lam := BinaryControllerExecution.fromPublic parameters.lam
  let cap := BinaryControllerExecution.fromPublic U
  ⟨⟨primes.value,sizes.value,lam.value,cap.value,
      (prepareStaticPrimes_project labels).trans hlabels,
      (prepareStaticCounts_project publicSizes.value).trans (formBlockSizes_value n h),
      BinaryControllerExecution.fromPublic_nview parameters.lam,
      BinaryControllerExecution.fromPublic_nview U⟩,
    primes.bitSteps+sizes.bitSteps+lam.bitSteps+cap.bitSteps,
    publicSizes.controlSites+primes.controlSites+sizes.controlSites+lam.controlSites+cap.controlSites+8,
    primes.arithSites+sizes.arithSites+lam.arithSites+cap.arithSites⟩

def controllerFormationSites (n h P : ℕ) : ℕ :=
  74*EndToEndAPSP.incidenceSize n h+14*P+14*n*n+20

structure Backend (n h : ℕ) (Payload : Type) where
  oracle : IntTable n → IntTable n → IntTable n →
    BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n h) Payload
  correct : ∀ A B T, (oracle A B T).project.Correct
    (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T))

def controllerExec {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    BinaryControllerExecution.Result
      (BinaryControllerExecution.StageResult parameters.pool.card (EndToEndAPSP.incidenceSize n h) (n*n) Payload) :=
  let owner := formOwner n h
  let initial := formInitial n h
  let remaining := formFlags parameters.pool.card true
  let marked := formFlags (n*n) false
  let controller := BinaryControllerExecution.restartsExec (backend.oracle A B T) owner.value
    static.primes static.blockSizes remaining.value parameters.k static.lam parameters.stages
    initial.value marked.value
  { controller with controlSites := controller.controlSites+owner.controlSites+initial.controlSites+
      remaining.controlSites+marked.controlSites+12 }

@[simp] theorem controllerExec_value {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (controllerExec backend parameters static A B T).value=
      (BinaryControllerExecution.restartsExec (backend.oracle A B T) (EndToEndAPSP.ownerTable n h)
        static.primes static.blockSizes (Vector.replicate parameters.pool.card true)
        parameters.k static.lam parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)).value := by
  simp only [controllerExec,formOwner_value,formInitial_value,formFlags_value]

 theorem controllerExec_control {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (controllerExec backend parameters static A B T).controlSites=
      (BinaryControllerExecution.restartsExec (backend.oracle A B T) (EndToEndAPSP.ownerTable n h)
        static.primes static.blockSizes (Vector.replicate parameters.pool.card true)
        parameters.k static.lam parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)).controlSites+
          controllerFormationSites n h parameters.pool.card := by
  simp only [controllerExec,formOwner_value,formInitial_value,formFlags_value,formOwner_control,
    formInitial_control,formFlags_control,controllerFormationSites]
  ring

theorem controllerExec_project {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (controllerExec backend parameters static A B T).value.project =
      CountedArrayComposite.restarts (backend.oracle A B T).project (EndToEndAPSP.ownerTable n h)
        (EndToEndAPSP.primeVector parameters.pool) (EndToEndAPSP.blockSizeTable n h)
        (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
        (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false) := by
  simp only [controllerExec_value,BinaryControllerExecution.restartsExec_project,
    static.primes_eq,static.blockSizes_eq,static.lam_eq]

theorem controllerExec_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).block i →
      ((EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).value i k).natAbs ≤ U) :
    let out := (controllerExec backend parameters static A B T).value
    (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).StateInvariant
      (EndToEndAPSP.ownerTable n h).get (ArrayCompositeAlgorithm.decode (EndToEndAPSP.initialFlags n h))
      (ArrayCompositeAlgorithm.decode out.active) (ArrayCompositeAlgorithm.decode out.marked) ∧
    2^parameters.stages*(ArrayCompositeAlgorithm.decode out.active).card ≤
      n^2*CompactBlocks.blockCount n h := by
  let inst := EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)
  have hfalse : ArrayCompositeAlgorithm.decode (Vector.replicate (n*n) false) = ∅ := by
    ext i
    simp [ArrayCompositeAlgorithm.mem_decode]
  have hinv := inst.initial_invariant (EndToEndAPSP.ownerTable n h).get
    (ArrayCompositeAlgorithm.decode (EndToEndAPSP.initialFlags n h))
  have hc := ArrayCompositeAlgorithm.restarts_correct (backend.oracle A B T).project.erase inst
    (backend.correct A B T) (EndToEndAPSP.ownerTable n h)
    (EndToEndAPSP.primeVector parameters.pool) (EndToEndAPSP.primeVector_injective parameters.pool)
    (ArrayCompositeAlgorithm.decode (EndToEndAPSP.initialFlags n h)) (EndToEndAPSP.initialFlags n h)
    (Vector.replicate (n*n) false) (EndToEndAPSP.blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.M parameters.lam h parameters.stages
    (by simpa only [hfalse] using hinv)
    (fun i _ => EndToEndAPSP.blockSizeTable_correct hh (viewTable A) (viewTable B) (viewTable T) i)
    parameters.threshold (by simpa only [EndToEndAPSP.primeVector_pool] using parameters.size)
    (by simpa only [EndToEndAPSP.primeVector_pool] using
      CertificationParameters.parameters_divisorBound parameters inst hmag)
    (fun i _ => CompactBlocks.block_card_le hh ((EndToEndAPSP.incidenceEquiv n h).symm i).2.1) parameters.rate
  have he := CountedArrayComposite.restarts_erases (backend.oracle A B T).project
    (EndToEndAPSP.ownerTable n h) (EndToEndAPSP.primeVector parameters.pool)
    (EndToEndAPSP.blockSizeTable n h) (Vector.replicate parameters.pool.card true)
    parameters.k parameters.lam parameters.stages (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  rw [← he, ← controllerExec_project backend parameters static A B T] at hc
  simpa only [CountedArrayComposite.StageResult.erase,BinaryControllerExecution.StageResult.project,
    EndToEndAPSP.initialFlags_card] using hc

/-- The binary controller is run once; finalization reads only its retained fields. -/
def solve {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    Finished n h (BinaryControllerExecution.Call (EndToEndAPSP.incidenceSize n h) Payload) :=
  let controller := controllerExec backend parameters static A B T
  finalize controller.value.active controller.value.marked controller.value.calls controller.value.backendWork
    controller.bitSteps controller.controlSites A B T

theorem solve_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).block i →
      ((EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).value i k).natAbs ≤ U)
    (i j : Fin n) : StoredMinPlusAPSP.decode (solve backend parameters static A B T).answers i j=true ↔
      ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+BinaryCell.view (read T i j)=0 :=
  finalize_correct_of_invariant hh _ _ _ _ _ _ A B T
    (controllerExec_correct hh backend parameters static A B T hmag).1 i j

theorem solve_scan_budget {n h U : ℕ} {Payload : Type} (hh : 0 < h) (hhn : h ≤ n)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (hs : (2*n).size ≤ parameters.stages) (A B T : IntTable n)
    (hmag : ∀ i k, k ∈ (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).block i →
      ((EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).value i k).natAbs ≤ U) :
    (solve backend parameters static A B T).originalSumTests ≤ n^2 :=
  finalize_scan_budget hhn hs _ _ _ _ _ _ A B T
    (controllerExec_correct hh backend parameters static A B T hmag).2

theorem solve_provenance {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    ∀ call ∈ (solve backend parameters static A B T).calls,
      call.result=(backend.oracle A B T).table call.factors.selected call.factors.candidate call.factors.active :=
by
  change ∀call∈(controllerExec backend parameters static A B T).value.calls,_
  rw [controllerExec_value]
  exact BinaryControllerExecution.restartsExec_retained_results _ _ _ _ _ _ _ _ _ _

theorem solve_backendWork {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (solve backend parameters static A B T).backendWork =
      CountedArrayComposite.workSum (BinaryControllerExecution.projectCalls (solve backend parameters static A B T).calls) :=
by
  change (controllerExec backend parameters static A B T).value.backendWork =
    CountedArrayComposite.workSum (BinaryControllerExecution.projectCalls
      (controllerExec backend parameters static A B T).value.calls)
  rw [controllerExec_value]
  exact BinaryControllerExecution.restartsExec_backendWork _ _ _ _ _ _ _ _ _ _

theorem capTest_true {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (atMost (entryBound A B T).value static.cap.cell).value=true ↔
      CountedEndToEndAPSP.entryQueryBound (viewTable A) (viewTable B) (viewTable T) ≤ U := by
  have hcap : BinaryCell.view static.cap.cell = (U : ℤ) := by
    rw [← BinaryControllerExecution.nview_cast,static.cap_eq]
  rw [atMost_true _ _ (by rw [entryBound_view]; positivity) static.cap.nonnegative,
    entryBound_view,hcap]
  exact_mod_cast Iff.rfl

abbrev FastPayload (n h : ℕ) (Payload : Type) :=
  Finished n h (BinaryControllerExecution.Call (EndToEndAPSP.incidenceSize n h) Payload)

structure CallbackPayload (n h : ℕ) (Payload : Type) where
  cap : Option (FFTBitCost.BinaryResult Cell × FFTBitCost.BinaryResult Bool)
  execution : Sum (FastPayload n h Payload) (DirectPayload n)

def finishedWork {n h : ℕ} {Call : Type} (addressPrice : ℕ) (out : Finished n h Call) : ℕ :=
  out.backendWork+out.bitSteps+addressPrice*out.controlSites

/-- The cap check, one controller execution, and final scan returns are retained.
`addressPrice` prices the separate bounded-index IR operations, not coefficient arithmetic. -/
def callback {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters)
    (addressPrice : ℕ) : BinaryAPSPCaller.Oracle n (CallbackPayload n h Payload) := fun A B T =>
  let largest := entryBound A B T
  let checked := atMost largest.value static.cap.cell
  let capWork := largest.bitSteps+checked.bitSteps+addressPrice*(12*n*n+5)
  if checked.value then
    let out := solve backend parameters static A B T
    { answers := out.answers
      payload := ⟨some (largest,checked),Sum.inl out⟩
      work := capWork+finishedWork addressPrice out
      answerWrites := n*n+out.denseAnswerWrites+out.finalScatterWrites }
  else
    let out := directOracle n A B T
    { answers := out.answers
      payload := ⟨some (largest,checked),Sum.inr out.payload⟩
      work := capWork+out.payload.bitSteps+addressPrice*out.payload.controlSites
      answerWrites := out.answerWrites }

theorem callback_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (addressPrice : ℕ) (A B T : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode (callback backend parameters static addressPrice A B T).answers i j=true ↔
      ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+BinaryCell.view (read T i j)=0 := by
  unfold callback
  dsimp only
  split_ifs with hcap
  · apply solve_correct hh backend parameters static A B T _ i j
    intro x k _
    exact (CountedEndToEndAPSP.entryQueryBound_flat (viewTable A) (viewTable B) (viewTable T) x k).trans
      ((capTest_true parameters static A B T).mp hcap)
  · exact directOracle_correct n A B T i j

theorem callback_refines_aligned {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (static : Static (n:=n) parameters) (addressPrice : ℕ) :
    BinaryAPSPCaller.Refines (callback backend parameters static addressPrice)
      (CountedEndToEndAPSP.callback (AlignedAPSP.backend n h hh) parameters) := by
  intro A B T
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  apply Bool.eq_iff_iff.mpr
  change StoredMinPlusAPSP.decode (callback backend parameters static addressPrice A B T).answers ⟨i,hi⟩ ⟨j,hj⟩=true ↔
    StoredMinPlusAPSP.decode (CountedEndToEndAPSP.callback (AlignedAPSP.backend n h hh) parameters
      (viewTable A) (viewTable B) (viewTable T)).answers ⟨i,hi⟩ ⟨j,hj⟩=true
  exact (callback_correct hh backend parameters static addressPrice A B T ⟨i,hi⟩ ⟨j,hj⟩).trans
    (by simpa only [viewTable_read] using
      (CountedEndToEndAPSP.callback_correct hh (AlignedAPSP.backend n h hh) parameters
        (viewTable A) (viewTable B) (viewTable T) ⟨i,hi⟩ ⟨j,hj⟩).symm)

structure PreparedOracle (n h : ℕ) (Payload : Type) where
  oracle : BinaryAPSPCaller.Oracle n (CallbackPayload n h Payload)
  setupBits : ℕ
  setupControl : ℕ

/-- Configuration and public binary setup are selected before the adaptive-input lambda. -/
def prepareOracle {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (configuration : Option (CompleteAPSP.Parameters h U)) (addressPrice : ℕ) : PreparedOracle n h Payload :=
  match configuration with
  | none =>
    ⟨(fun A B T =>
      let out := directOracle n A B T
      { answers := out.answers,payload := ⟨none,Sum.inr out.payload⟩,
        work := out.payload.bitSteps+addressPrice*out.payload.controlSites,
        answerWrites := out.answerWrites }),0,1⟩
  | some parameters =>
    let setup := setupStatic (n:=n) parameters
    ⟨callback backend parameters setup.value addressPrice,setup.bitSteps,setup.controlSites+1⟩

theorem prepareOracle_correct {n h U : ℕ} {Payload : Type} (hh : 0 < h)
    (backend : Backend n h Payload) (configuration : Option (CompleteAPSP.Parameters h U))
    (addressPrice : ℕ) (A B T : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode ((prepareOracle backend configuration addressPrice).oracle A B T).answers i j=true ↔
      ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+BinaryCell.view (read T i j)=0 := by
  cases configuration with
  | none => exact directOracle_correct n A B T i j
  | some p => exact callback_correct hh backend p _ addressPrice A B T i j

theorem solve_projectCalls {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    BinaryControllerExecution.projectCalls (solve backend parameters static A B T).calls =
      (CountedArrayComposite.restarts (backend.oracle A B T).project (EndToEndAPSP.ownerTable n h)
        (EndToEndAPSP.primeVector parameters.pool) (EndToEndAPSP.blockSizeTable n h)
        (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
        (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)).calls :=
  congrArg CountedArrayComposite.StageResult.calls (controllerExec_project backend parameters static A B T)

theorem solve_calls_bound {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (solve backend parameters static A B T).calls.length ≤ parameters.stages*(parameters.k+1)*parameters.pool.card := by
  have he := congrArg List.length (solve_projectCalls backend parameters static A B T)
  simp only [BinaryControllerExecution.projectCalls,List.length_map] at he
  rw [he]
  exact CountedArrayComposite.restarts_calls_bound _ _ _ _ _ _ _ _ _ _

theorem solve_factor_property {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n)
    (property : ℕ → Prop) (hproperty : ∀p∈parameters.pool,property p) :
    ∀ call ∈ (solve backend parameters static A B T).calls,
      ∀ p ∈ call.factors.selected++[call.factors.candidate],property p := by
  have hp := CountedArrayComposite.restarts_factors_property (backend.oracle A B T).project
    (EndToEndAPSP.ownerTable n h) (EndToEndAPSP.primeVector parameters.pool) property
    (fun i=>hproperty _ (EndToEndAPSP.primeVector_mem _ i)) (EndToEndAPSP.blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  intro call hc
  apply hp call.project
  rw [←solve_projectCalls backend parameters static A B T]
  exact List.mem_map.mpr ⟨call,hc,rfl⟩

theorem solve_valid_histories {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n)
    (hthree : ∀p∈parameters.pool,p≠3) :
    ∀ call ∈ (solve backend parameters static A B T).calls,
      EndToEndAPSP.ValidFactors (call.factors.selected++[call.factors.candidate]) := by
  have hd := CountedArrayComposite.restarts_factors_distinct (backend.oracle A B T).project
    (EndToEndAPSP.ownerTable n h) (EndToEndAPSP.primeVector parameters.pool)
    (EndToEndAPSP.primeVector_injective parameters.pool) (EndToEndAPSP.blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  have hp := solve_factor_property backend parameters static A B T (fun p=>Nat.Prime p∧p≠3)
    (fun p hp=>⟨parameters.prime p hp,hthree p hp⟩)
  intro call hc
  refine ⟨?_,hp call hc⟩
  apply hd call.project
  rw [←solve_projectCalls backend parameters static A B T]
  exact List.mem_map.mpr ⟨call,hc,rfl⟩

theorem solve_factors_length {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    ∀ call ∈ (solve backend parameters static A B T).calls,
      call.factors.selected.length+1≤parameters.k+1 := by
  have hl := CountedArrayComposite.restarts_factors_length_le (backend.oracle A B T).project
    (EndToEndAPSP.ownerTable n h) (EndToEndAPSP.primeVector parameters.pool) (EndToEndAPSP.blockSizeTable n h)
    (Vector.replicate parameters.pool.card true) parameters.k parameters.lam parameters.stages
    (EndToEndAPSP.initialFlags n h) (Vector.replicate (n*n) false)
  intro call hc
  apply hl call.project
  rw [←solve_projectCalls backend parameters static A B T]
  exact List.mem_map.mpr ⟨call,hc,rfl⟩

theorem controllerExec_visits_bound {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (static : Static (n:=n) parameters) (A B T : IntTable n) :
    (controllerExec backend parameters static A B T).value.controllerVisits ≤
      parameters.stages*(parameters.k*CountedArrayComposite.batchVisits parameters.pool.card
        (EndToEndAPSP.incidenceSize n h)+CountedArrayComposite.finalVisits parameters.pool.card
          (EndToEndAPSP.incidenceSize n h)) := by
  have he:=congrArg CountedArrayComposite.StageResult.controllerVisits
    (controllerExec_project backend parameters static A B T)
  rw [show (controllerExec backend parameters static A B T).value.controllerVisits = _ from he]
  exact CountedArrayComposite.restarts_visits_bound _ _ _ _ _ _ _ _ _ _

/-- Public bounded label arithmetic selects the original middle block.
Only selected stored coefficients enter the bit-circuit sum test. -/
def zeroSlotTest {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) (k : Fin n) : SlotResult :=
  let x := (EndToEndAPSP.incidenceEquiv n h).symm i
  if k.val/h = x.2.1.val then
    let tested := sumZero (read A x.1.1 k) (read B k x.1.2) (read T x.1.1 x.1.2) (window x.2.2)
    ⟨tested.value,tested.bitSteps,12⟩
  else ⟨false,0,6⟩

 theorem zeroSlotTest_true {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) (k : Fin n) :
    (zeroSlotTest A B T i k).value = true ↔
      k ∈ (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).block i ∧
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).value i k = 0 := by
  simp only [zeroSlotTest,EndToEndAPSP.flatInstance,CompleteAPSP.incidenceInstance,
    CompactBlocks.block,Finset.mem_filter,Finset.mem_univ,true_and,viewTable_read]
  split_ifs with hg
  · simp only [hg,true_and,sumZero_true,window_view]
  · simp only [hg,false_and]

/-- Exact zero-modulus fallback, storing every joint child before using its
value and counters. Successful tests increment maintained binary counts. -/
def zeroCountScan {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    List (Fin n) → BinaryControllerExecution.Result BinaryControllerExecution.NatCell
  | [] => ⟨BinaryControllerExecution.zero,0,1,0⟩
  | k :: ks =>
    let tail := zeroCountScan A B T i ks
    let tested := zeroSlotTest A B T i k
    if tested.value then
      let increment := BinaryControllerExecution.add tail.value BinaryControllerExecution.one
      ⟨increment.value,tail.bitSteps+tested.bitSteps+increment.bitSteps,
        tail.controlSites+tested.controlSites+increment.controlSites+5,tail.arithSites+1⟩
    else
      ⟨tail.value,tail.bitSteps+tested.bitSteps,tail.controlSites+tested.controlSites+4,tail.arithSites⟩

 theorem zeroCountScan_nview {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) (ks : List (Fin n)) :
    BinaryControllerExecution.nview (zeroCountScan A B T i ks).value =
      (ks.map (fun k => if (zeroSlotTest A B T i k).value then 1 else 0)).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [zeroCountScan,List.map_cons,List.sum_cons]
    cases hz : (zeroSlotTest A B T i k).value <;>
      simp [BinaryControllerExecution.add_nview,ih,Nat.add_comm]

/-- Scan the original labels once, including the zero-count empty case. -/
def zeroCount {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.Result BinaryControllerExecution.NatCell :=
  zeroCountScan A B T i (List.finRange n)

 theorem zeroCount_sum {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview (zeroCount A B T i).value =
      ∑ k : Fin n, if (zeroSlotTest A B T i k).value then 1 else 0 := by
  rw [zeroCount,zeroCountScan_nview]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem zeroBoolCount_modCount {n : ℕ} {X : Type*}
    (F : CompositeCertification.Instance X (Fin n)) (i : X) (test : Fin n → Bool)
    (htest : ∀ k, test k = true ↔ k ∈ F.block i ∧ F.value i k = 0) :
    (∑ k : Fin n, if test k then 1 else 0) = F.modCount 0 i := by
  simp only [CompositeCertification.Instance.modCount, Nat.cast_zero, zero_dvd_iff]
  have hp : ∀ k : Fin n, (if test k then 1 else 0 : ℕ) =
      if k ∈ F.block i then (if F.value i k = 0 then 1 else 0) else 0 := by
    intro k
    by_cases hb : k ∈ F.block i <;> by_cases hz : F.value i k = 0 <;>
      simp_all
  simp_rw [hp]
  have hfilter : Finset.univ.filter (fun k => k ∈ F.block i) = F.block i := by
    ext k
    simp
  rw [← Finset.sum_filter, hfilter]

theorem zeroModCount_le_card {n : ℕ} {X : Type*}
    (F : CompositeCertification.Instance X (Fin n)) (d : ℕ) (i : X) :
    F.modCount d i ≤ (F.block i).card := by
  unfold CompositeCertification.Instance.modCount
  calc
    _ ≤ ∑ _k ∈ F.block i, 1 := Finset.sum_le_sum (fun _ _ => by split <;> omega)
    _ = _ := by simp


 theorem zeroCount_nview {n h : ℕ} (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview (zeroCount A B T i).value =
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount 0 i := by
  rw [zeroCount_sum]
  exact zeroBoolCount_modCount _ i (fun k => (zeroSlotTest A B T i k).value)
    (fun k => zeroSlotTest_true A B T i k)

 theorem zeroCount_le {n h : ℕ} (hh : 0 < h) (A B T : IntTable n)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview (zeroCount A B T i).value ≤ h := by
  rw [zeroCount_nview]
  exact (zeroModCount_le_card _ _ _).trans
    (CompactBlocks.block_card_le hh ((EndToEndAPSP.incidenceEquiv n h).symm i).2.1)

theorem setupStaticFromPrimes_control {n h U : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) :
    (setupStaticFromPrimes (n:=n) parameters labels hlabels).controlSites =
      (setupStatic (n:=n) parameters).controlSites+45*EndToEndAPSP.incidenceSize n h+2 := by
  simp only [setupStaticFromPrimes,setupStatic,formBlockSizes_value,formBlockSizes_control,hlabels]
  ring

theorem setupStaticFromPrimes_control_public {n h U Wp : ℕ} (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool)
    (hp : ∀i,(labels.get i).size≤Wp) :
    (setupStaticFromPrimes (n:=n) parameters labels hlabels).controlSites ≤
      parameters.pool.card*(8*Wp+18)+EndToEndAPSP.incidenceSize n h*(8*h.size+61)+
        8*parameters.lam.size+8*U.size+20 := by
  rw [setupStaticFromPrimes_control]
  have hs:=setupStatic_control_public (n:=n) parameters (by simpa only [←hlabels] using hp)
  calc
    _ ≤ (parameters.pool.card*(8*Wp+18)+EndToEndAPSP.incidenceSize n h*(8*h.size+16)+
        8*parameters.lam.size+8*U.size+18)+45*EndToEndAPSP.incidenceSize n h+2 :=
      Nat.add_le_add_right (Nat.add_le_add_right hs _) _
    _ = _ := by ring

/-- Use a retained sorted-label vector. The label-array formation is charged
once here, in addition to binary serialization and block-size formation. -/
def prepareOracleFromPrimes {n h U : ℕ} {Payload : Type} (backend : Backend n h Payload)
    (parameters : CompleteAPSP.Parameters h U) (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) (addressPrice : ℕ) :
    PreparedOracle n h Payload :=
  let setup:=setupStaticFromPrimes (n:=n) parameters labels hlabels
  ⟨callback backend parameters setup.value addressPrice,setup.bitSteps,
    setup.controlSites+parameters.pool.card+1⟩

theorem prepareOracleFromPrimes_correct {n h U : ℕ} {Payload : Type} (hh : 0<h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool)
    (addressPrice : ℕ) (A B T : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode ((prepareOracleFromPrimes backend parameters labels hlabels addressPrice).oracle
      A B T).answers i j=true ↔ ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+
        BinaryCell.view (read T i j)=0 :=
  callback_correct hh backend parameters _ addressPrice A B T i j

theorem prepareOracleFromPrimes_refines_aligned {n h U : ℕ} {Payload : Type} (hh : 0<h)
    (backend : Backend n h Payload) (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool)
    (addressPrice : ℕ) :
    BinaryAPSPCaller.Refines (prepareOracleFromPrimes backend parameters labels hlabels addressPrice).oracle
      (CountedEndToEndAPSP.callback (AlignedAPSP.backend n h hh) parameters) :=
  callback_refines_aligned hh backend parameters _ addressPrice

/-- The actual producer return, public history work, and exceptional exact
count return are retained in one controller table payload. -/
structure HistoryPayload (n h : ℕ) where
  factors : List ℕ
  metadataSites : ℕ
  positive : Option (BinaryControllerExecution.Result
    (BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (BinaryFoldedFactory.Payload n h)))
  zero : Option (BinaryControllerExecution.Result
    (BinaryControllerExecution.Counts (EndToEndAPSP.incidenceSize n h)))

def positiveTable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (A B T : IntTable n)
    (factors : List ℕ) (metadataSites addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (HistoryPayload n h) :=
  let produced:=BinaryFoldedFactory.produce f p ⟨A,B,T⟩
  { counts:=produced.value.counts
    payload:=⟨factors,metadataSites,some produced,none⟩
    work:=addressPrice*(produced.value.work+metadataSites) }

theorem positiveTable_modCount {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (A B T : IntTable n)
    (factors : List ℕ) (metadataSites addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((positiveTable f p A B T factors metadataSites addressPrice).counts.get i)=
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount r i :=
  BinaryFoldedFactory.produce_modCount hh f p ⟨A,B,T⟩ i

theorem positiveTable_count_le {n h r : ℕ} (hh : 0<h) (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (A B T : IntTable n)
    (factors : List ℕ) (metadataSites addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((positiveTable f p A B T factors metadataSites addressPrice).counts.get i)≤h :=
  BinaryFoldedFactory.produce_count_le hh f p ⟨A,B,T⟩ i

/-- The exceptional zero-modulus branch scans original binary operands.
It is total and does not construct a reference prime or serialize a count. -/
def zeroTable {n h : ℕ} (A B T : IntTable n) (factors : List ℕ) (metadataSites addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (HistoryPayload n h) :=
  let counts:=BinaryControllerExecution.tabulate (fun i=>zeroCount A B T i)
  { counts:=counts.value
    payload:=⟨factors,metadataSites,none,some counts⟩
    work:=addressPrice*(counts.bitSteps+counts.controlSites+metadataSites) }

theorem zeroTable_modCount {n h : ℕ} (A B T : IntTable n)
    (factors : List ℕ) (metadataSites addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((zeroTable A B T factors metadataSites addressPrice).counts.get i)=
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount 0 i := by
  simp only [zeroTable,BinaryControllerExecution.tabulate_value,Vector.get_ofFn,zeroCount_nview]

theorem zeroTable_count_le {n h : ℕ} (hh : 0<h) (A B T : IntTable n)
    (factors : List ℕ) (metadataSites addressPrice : ℕ) (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((zeroTable A B T factors metadataSites addressPrice).counts.get i)≤h := by
  simp only [zeroTable,BinaryControllerExecution.tabulate_value,Vector.get_ofFn]
  exact zeroCount_le hh A B T i

def historySites (selected : List ℕ) : ℕ := 8*(selected.length+1)+20

/-- A total concrete factor-aware producer. Public factor validation and
split loops, public geometry loops, and the actual binary producer returns
are captured once. Active cells need no masking because all counts are exact. -/
def concreteTable {n h : ℕ} (A B T : IntTable n) (selected : List ℕ) (candidate : ℕ)
    (_active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ) :
    BinaryControllerExecution.Table (EndToEndAPSP.incidenceSize n h) (HistoryPayload n h) :=
  let factors:=selected++[candidate]
  let validation:=FactorValidation.validate factors
  if hb : validation.1=true then
    let split:=AlignedAPSP.prepareFactors AlignedCertificate.S factors
      ((FactorValidation.validate_correct factors).mp hb)
    let plan:=BinaryTriangleSetupCosts.preparePlan n h split.plan
    positiveTable split.plan plan.value A B T factors
      (historySites selected+validation.2+split.work+plan.sites) addressPrice
  else
    let product:=FactorValidation.splitProducts 0 factors
    let modulus:=product.1.2
    if hz : modulus=0 then
      zeroTable A B T factors (historySites selected+validation.2+product.2) addressPrice
    else
      let f:=CompactBlocks.scalarPhysicalPlan modulus hz
      let plan:=BinaryTriangleSetupCosts.preparePlan n h f
      positiveTable f plan.value A B T factors
        (historySites selected+validation.2+product.2+plan.sites) addressPrice

theorem concreteTable_modCount {n h : ℕ} (hh : 0<h) (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((concreteTable A B T selected candidate active addressPrice).counts.get i)=
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)).modCount
        (selected.prod*candidate) i := by
  have hp : (selected++[candidate]).prod=selected.prod*candidate := by simp
  have hprod : (FactorValidation.splitProducts 0 (selected++[candidate])).1.2=
      (selected++[candidate]).prod := by
    simpa only [List.drop_zero] using congrArg Prod.snd
      (FactorValidation.splitProducts_value 0 (selected++[candidate]))
  unfold concreteTable
  dsimp only
  split_ifs with hb hz
  · rw [positiveTable_modCount hh,hp]
  · rw [zeroTable_modCount]
    have hm : selected.prod*candidate=0 := hp.symm.trans (hprod.symm.trans hz)
    rw [hm]
  · rw [positiveTable_modCount hh,hprod,hp]

theorem concreteTable_count_le {n h : ℕ} (hh : 0<h) (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (i : Fin (EndToEndAPSP.incidenceSize n h)) :
    BinaryControllerExecution.nview ((concreteTable A B T selected candidate active addressPrice).counts.get i)≤h := by
  unfold concreteTable
  dsimp only
  split_ifs
  · exact positiveTable_count_le hh _ _ A B T _ _ addressPrice i
  · exact zeroTable_count_le hh A B T _ _ addressPrice i
  · exact positiveTable_count_le hh _ _ A B T _ _ addressPrice i

def concreteOracle {n h : ℕ} (A B T : IntTable n) (addressPrice : ℕ) :
    BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n h) (HistoryPayload n h) :=
  ⟨fun selected candidate active=>concreteTable A B T selected candidate active addressPrice⟩

theorem concreteOracle_correct {n h : ℕ} (hh : 0<h) (A B T : IntTable n) (addressPrice : ℕ) :
    (concreteOracle (h:=h) A B T addressPrice).project.Correct
      (EndToEndAPSP.flatInstance (h:=h) (viewTable A) (viewTable B) (viewTable T)) := by
  intro selected candidate active i _hi
  simpa only [concreteOracle,BinaryControllerExecution.Oracle.project,
    BinaryControllerExecution.Table.project,CountedArrayComposite.Oracle.erase,
    BinaryControllerExecution.projectCounts,Vector.get_map] using
      concreteTable_modCount hh A B T selected candidate active addressPrice i

theorem concreteOracle_countsBound {n h : ℕ} (hh : 0<h) (A B T : IntTable n) (addressPrice : ℕ) :
    BinaryControllerExecution.OracleCountsBound (concreteOracle (h:=h) A B T addressPrice) h :=
  fun selected candidate active i=>concreteTable_count_le hh A B T selected candidate active addressPrice i

/-- Concrete backend: no assumed triangle oracle or product correctness premise. -/
def concreteBackend (n h : ℕ) (hh : 0<h) (addressPrice : ℕ) : Backend n h (HistoryPayload n h) :=
  ⟨(fun A B T=>concreteOracle A B T addressPrice),fun A B T=>concreteOracle_correct hh A B T addressPrice⟩

theorem concreteTable_of_valid {n h : ℕ} (A B T : IntTable n) (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) (addressPrice : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate])) :
    let split:=AlignedAPSP.prepareFactors AlignedCertificate.S (selected++[candidate]) hv
    let plan:=BinaryTriangleSetupCosts.preparePlan n h split.plan
    concreteTable A B T selected candidate active addressPrice =
      positiveTable split.plan plan.value A B T (selected++[candidate])
        (historySites selected+(FactorValidation.validate (selected++[candidate])).2+split.work+plan.sites) addressPrice := by
  have hb:=(FactorValidation.validate_correct (selected++[candidate])).mpr hv
  simp only [concreteTable,dif_pos hb]

/-- The fully instantiated prepared callback. Its setup consumes the retained
prime labels, and its adaptive calls execute the concrete folded producer. -/
def prepareConcreteFromPrimes {n h U : ℕ} (hh : 0<h) (parameters : CompleteAPSP.Parameters h U)
    (labels : Vector ℕ parameters.pool.card) (hlabels : labels=EndToEndAPSP.primeVector parameters.pool)
    (addressPrice : ℕ) : PreparedOracle n h (HistoryPayload n h) :=
  prepareOracleFromPrimes (concreteBackend n h hh addressPrice) parameters labels hlabels addressPrice

theorem prepareConcreteFromPrimes_correct {n h U : ℕ} (hh : 0<h)
    (parameters : CompleteAPSP.Parameters h U) (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) (addressPrice : ℕ)
    (A B T : IntTable n) (i j : Fin n) :
    StoredMinPlusAPSP.decode ((prepareConcreteFromPrimes hh parameters labels hlabels addressPrice).oracle
      A B T).answers i j=true ↔ ∃ k, BinaryCell.view (read A i k)+BinaryCell.view (read B k j)+
        BinaryCell.view (read T i j)=0 :=
  prepareOracleFromPrimes_correct hh _ parameters labels hlabels addressPrice A B T i j

theorem prepareConcreteFromPrimes_refines_aligned {n h U : ℕ} (hh : 0<h)
    (parameters : CompleteAPSP.Parameters h U) (labels : Vector ℕ parameters.pool.card)
    (hlabels : labels=EndToEndAPSP.primeVector parameters.pool) (addressPrice : ℕ) :
    BinaryAPSPCaller.Refines (prepareConcreteFromPrimes hh parameters labels hlabels addressPrice).oracle
      (CountedEndToEndAPSP.callback (AlignedAPSP.backend n h hh) parameters) :=
  prepareOracleFromPrimes_refines_aligned hh _ parameters labels hlabels addressPrice

#print axioms sumZero_true
#print axioms sumZero_price
#print axioms slotTest_value
#print axioms scanSlots_value
#print axioms scanSlots_tests
#print axioms scanSlots_price

#print axioms absolute_view
#print axioms maxAbs_view
#print axioms maxAbs_size
#print axioms maxAbs_width
#print axioms maxAbs_price
#print axioms isZero_true
#print axioms entryMax_view
#print axioms entryMax_price
#print axioms entryBound_view
#print axioms atMost_true
#print axioms atMost_price
#print axioms directOracle_answers
#print axioms directOracle_correct
#print axioms directOracle_tests
#print axioms directOracle_price
#print axioms finalScans_project
#print axioms finalScans_tests
#print axioms finalScans_price
#print axioms entryBound_size
#print axioms entryBound_price_explicit
#print axioms finalize_correct_of_invariant
#print axioms finalize_scan_budget
#print axioms finalize_price
#print axioms setupStatic_control_public
#print axioms controllerExec_project
#print axioms controllerExec_correct
#print axioms solve_correct
#print axioms solve_scan_budget
#print axioms solve_provenance
#print axioms solve_backendWork
#print axioms callback_correct
#print axioms callback_refines_aligned
#print axioms prepareOracle_correct
#print axioms solve_calls_bound
#print axioms solve_valid_histories
#print axioms solve_factors_length
#print axioms controllerExec_visits_bound
#print axioms zeroCount_nview
#print axioms zeroCount_le
#print axioms controllerExec_control
#print axioms setupStaticFromPrimes_control_public
#print axioms prepareOracleFromPrimes_correct
#print axioms prepareOracleFromPrimes_refines_aligned
#print axioms positiveTable_modCount
#print axioms zeroTable_modCount
#print axioms concreteTable_modCount
#print axioms concreteOracle_correct
#print axioms concreteOracle_countsBound
#print axioms concreteTable_of_valid
#print axioms prepareConcreteFromPrimes_correct
#print axioms prepareConcreteFromPrimes_refines_aligned
end ThinMatrix.BinaryTriangleExecution
