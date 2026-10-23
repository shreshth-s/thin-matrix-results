import DistinguishedResidualSupport
import BinaryModularCell

set_option autoImplicit false

/-! Retained physical-position layouts constructed from an input mask. The
inverse positions are found by binary increment circuits and charged decoding.
List traversal, filtering, array creation and indexing have separate explicit
bounded-register/control counts; these counts are not a machine compilation. -/
namespace ThinMatrix.ResidualLayout
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open DistinguishedResidualSupport
open scoped BigOperators

def selected {L : ℕ} (mask : Vector Bool L) : List (Fin L) := (List.finRange L).filter mask.get

def remaining {L : ℕ} (mask : Vector Bool L) : List (Fin L) := (List.finRange L).filter (fun i => !mask.get i)

@[simp] theorem mem_selected {L : ℕ} (mask : Vector Bool L) (i : Fin L) :
    i∈selected mask ↔ mask.get i=true := by simp [selected]
@[simp] theorem mem_remaining {L : ℕ} (mask : Vector Bool L) (i : Fin L) :
    i∈remaining mask ↔ mask.get i=false := by simp [remaining]

theorem selected_nodup {L : ℕ} (mask : Vector Bool L) : (selected mask).Nodup := (List.nodup_finRange L).filter _
theorem remaining_nodup {L : ℕ} (mask : Vector Bool L) : (remaining mask).Nodup := (List.nodup_finRange L).filter _

theorem lengths {L : ℕ} (mask : Vector Bool L) : (selected mask).length+(remaining mask).length=L := by
  have h (xs : List (Fin L)) : (xs.filter mask.get).length+(xs.filter (fun i => !mask.get i)).length=xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases hx : mask.get x <;> simp [hx] <;> omega
  simpa [selected,remaining] using h (List.finRange L)

def search {L : ℕ} (i : Fin L) : List (Fin L) → Run Cell
  | [] => ⟨zero,0,2⟩
  | x::xs => if i=x then ⟨zero,0,6⟩ else
      let rest := search i xs
      let out := add BinaryModularCell.one rest.value
      ⟨out.value,rest.bitSteps+out.bitSteps,rest.control+8⟩

theorem search_view {L : ℕ} (i : Fin L) (xs : List (Fin L)) :
    view (search i xs).value=(xs.idxOf i : ℤ) := by
  induction xs with
  | nil => simp [search]
  | cons x xs ih =>
    by_cases h : i=x
    · subst i; simp [search]
    · simp [search,h,ih,List.idxOf_cons_ne,Ne.symm h,Nat.cast_add,add_comm]

theorem search_width {L : ℕ} (i : Fin L) (xs : List (Fin L)) (N : ℕ) (h : xs.length≤N) :
    (view (search i xs).value).natAbs.size≤N.size := by
  rw [search_view,Int.natAbs_natCast]
  exact Nat.size_le_size ((List.idxOf_le_length).trans h)

theorem search_bits {L : ℕ} (i : Fin L) (xs : List (Fin L)) (N : ℕ) (h : xs.length≤N) :
    (search i xs).bitSteps≤xs.length*BackendScalarBits.backendScalarUnit (N.size+1) := by
  induction xs with
  | nil => simp [search]
  | cons x xs ih =>
    have ht := ih (by simp only [List.length_cons] at h; omega)
    have hw := search_width i xs N (by simp only [List.length_cons] at h; omega)
    have ha := add_price (N.size+1) BinaryModularCell.one (search i xs).value (by simp) (hw.trans (by omega))
    simp only [search,List.length_cons]
    split <;> (try dsimp only) <;> nlinarith

theorem search_control {L : ℕ} (i : Fin L) (xs : List (Fin L)) :
    (search i xs).control≤8*xs.length+2 := by
  induction xs with
  | nil => simp [search]
  | cons x xs ih => simp only [search,List.length_cons]; split <;> (try dsimp only) <;> omega

def locate {L : ℕ} (i : Fin L) (xs : List (Fin L)) : Run ℕ :=
  let found := search i xs
  let decoded := BinaryModularCell.decodeUnsigned found.value
  ⟨decoded.value,found.bitSteps+decoded.bitSteps,found.control+4⟩

theorem locate_value {L : ℕ} (i : Fin L) (xs : List (Fin L)) :
    (locate i xs).value=xs.idxOf i := by
  simp [locate,BinaryModularCell.decodeUnsigned_value,search_view]

def locateBudget (L : ℕ) : ℕ := L*BackendScalarBits.backendScalarUnit (L.size+1)+8*(L.size+1)^2

theorem locate_bits {L : ℕ} (i : Fin L) (xs : List (Fin L)) (h : xs.length≤L) :
    (locate i xs).bitSteps≤locateBudget L := by
  have hs := search_bits i xs L h
  have hw := search_width i xs L h
  have hd := BinaryModularCell.decodeUnsigned_price L.size (search i xs).value hw
  simp only [locate,locateBudget]
  nlinarith

theorem locate_control {L : ℕ} (i : Fin L) (xs : List (Fin L)) (h : xs.length≤L) :
    (locate i xs).control≤8*L+6 := by
  have hs := search_control i xs
  simp only [locate]
  omega

/-- Semantic equivalence uses exactly the order of the retained filtered lists. -/
def equivalence {L : ℕ} (mask : Vector Bool L) : Layout L (selected mask).length (remaining mask).length where
  toFun i := if h : mask.get i then Sum.inl ⟨(selected mask).idxOf i,List.idxOf_lt_length_iff.mpr ((mem_selected mask i).mpr h)⟩
    else Sum.inr ⟨(remaining mask).idxOf i,List.idxOf_lt_length_iff.mpr ((mem_remaining mask i).mpr (by simpa using h))⟩
  invFun s := match s with | .inl j => (selected mask).get j | .inr j => (remaining mask).get j
  left_inv i := by
    by_cases h : mask.get i=true
    · simp [h]
    · simp [h]
  right_inv s := by
    cases s with
    | inl j =>
      have hm := (mem_selected mask ((selected mask).get j)).mp (List.get_mem _ _)
      simp only [List.get_eq_getElem] at hm ⊢
      simp [hm,selected_nodup]
    | inr j =>
      have hm := (mem_remaining mask ((remaining mask).get j)).mp (List.get_mem _ _)
      simp only [List.get_eq_getElem] at hm ⊢
      simp [hm,remaining_nodup]

structure Stored (L : ℕ) where
  normalPositions : Array (Fin L)
  otherPositions : Array (Fin L)
  routes : Vector (Bool × ℕ) L

def build {L : ℕ} (mask : Vector Bool L) : Run (Stored L) :=
  let ns := selected mask
  let os := remaining mask
  let routes := tabulate mask (fun i =>
    let normal := mask.get i
    let out := locate i (if normal then ns else os)
    (⟨(normal,out.value),out.bitSteps,out.control+4⟩ : Run (Bool × ℕ)))
  ⟨⟨ns.toArray,os.toArray,routes.value⟩,routes.bitSteps,routes.control+24*mask.toArray.size+12⟩

theorem build_route {L : ℕ} (mask : Vector Bool L) (i : Fin L) :
    (build mask).value.routes.get i = match equivalence mask i with
      | .inl j => (true,j.val) | .inr j => (false,j.val) := by
  simp only [build,tabulate_get,locate_value,equivalence,Equiv.coe_fn_mk]
  by_cases hm : mask.get i=true
  · simp [hm]
  · have hn : mask.get i=false := by simpa using hm
    simp [hn]

theorem build_positions {L : ℕ} (mask : Vector Bool L) :
    (build mask).value.normalPositions=(selected mask).toArray ∧
    (build mask).value.otherPositions=(remaining mask).toArray := ⟨rfl,rfl⟩

theorem build_bits {L : ℕ} (mask : Vector Bool L) :
    (build mask).bitSteps≤L*locateBudget L := by
  apply tabulate_bits
  intro i
  apply locate_bits
  split
  · exact (List.length_filter_le _ _).trans (by simp)
  · exact (List.length_filter_le _ _).trans (by simp)

theorem build_control {L : ℕ} (mask : Vector Bool L) :
    (build mask).control≤L*(8*L+66)+20 := by
  have h := tabulate_control mask (fun i =>
    let normal := mask.get i
    let out := locate i (if normal then selected mask else remaining mask)
    (⟨(normal,out.value),out.bitSteps,out.control+4⟩ : Run (Bool × ℕ))) (W:=8*L+10) (by
      intro i
      have hc := locate_control i (if mask.get i then selected mask else remaining mask) (by
        split <;> exact (List.length_filter_le _ _).trans (by simp))
      dsimp only
      omega)
  simp only [build,Vector.size_toArray]
  nlinarith

theorem equivalence_distinguished {L : ℕ} (mask : Vector Bool L) (i : Fin L) :
    (∃ j, equivalence mask i=Sum.inl j) ↔ mask.get i=true := by
  by_cases h : mask.get i=true <;> simp [equivalence,h]

/-- Materialize a physical word from retained routing entries. This copies
bounded alphabet/register values; coefficient cells use binary copy instead. -/
def assembleWord {A : Type} {L : ℕ} (layout : Stored L) (a b : Array A) (fallback : A) : Run (Vector A L) :=
  tabulate layout.routes (fun i =>
    let route := layout.routes.get i
    ⟨(if route.1 then a else b)[route.2]?.getD fallback,0,6⟩)

theorem assembleWord_value {A : Type} {L : ℕ} (mask : Vector Bool L)
    (a : Vector A (selected mask).length) (b : Vector A (remaining mask).length) (fallback : A) (i : Fin L) :
    (assembleWord (build mask).value a.toArray b.toArray fallback).value.get i =
      assemble (equivalence mask) a.get b.get i := by
  simp only [assembleWord,tabulate_get,build_route]
  rcases he : equivalence mask i with j | j <;>
    simp [he,assemble,j.isLt]
  all_goals rfl

theorem assembleWord_bits {A : Type} {L : ℕ} (layout : Stored L) (a b : Array A) (fallback : A) :
    (assembleWord layout a b fallback).bitSteps=0 := by
  simp [assembleWord,tabulate_bits_eq]

theorem assembleWord_control {A : Type} {L : ℕ} (layout : Stored L) (a b : Array A) (fallback : A) :
    (assembleWord layout a b fallback).control≤38*L+8 := by
  have h := tabulate_control layout.routes (fun i =>
    let route := layout.routes.get i
    (⟨(if route.1 then a else b)[route.2]?.getD fallback,0,6⟩ : Run A)) (fun _ => le_refl 6)
  simpa only [assembleWord,Nat.mul_comm] using h

#print axioms mem_selected
#print axioms mem_remaining
#print axioms selected_nodup
#print axioms remaining_nodup
#print axioms lengths
#print axioms search_view
#print axioms search_width
#print axioms search_bits
#print axioms search_control
#print axioms locate_value
#print axioms locate_bits
#print axioms locate_control
#print axioms equivalence
#print axioms build_route
#print axioms build_positions
#print axioms build_bits
#print axioms build_control
#print axioms equivalence_distinguished
#print axioms assembleWord_value
#print axioms assembleWord_bits
#print axioms assembleWord_control
end ThinMatrix.ResidualLayout
