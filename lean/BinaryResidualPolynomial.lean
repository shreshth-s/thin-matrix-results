import BinaryGroupedPreparation
import DistinguishedResidualRoot

set_option autoImplicit false

/-! Retained binary coefficient operations for the shifted distinguished
normal row. Every formal degree and every coefficient column is written.
Columns may contain full cyclic residues and repeated batch/request entries.
No polynomial evaluation, selected-coefficient projection, semantic integer
re-encoding, or multiplication oracle is used. -/
namespace ThinMatrix.BinaryResidualPolynomial
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators

abbrev Block (F C : ℕ) := Vector (Vector Cell C) F

def cellView {F C : ℕ} (a : Block F C) (d : Fin F) (r : Fin C) : ℤ := view ((a.get d).get r)
def Bound {F C : ℕ} (A : ℕ) (a : Block F C) : Prop := ∀ d r, (cellView a d r).natAbs≤A

/-- Four copied operands, four arithmetic operations, then an output copy. -/
def combine (a b c previous : Cell) : Run Cell :=
  let aa := copy a
  let bb := copy b
  let cc := copy c
  let pp := copy previous
  let na := neg aa.value
  let ab := sub na.value bb.value
  let abc := add ab.value cc.value
  let sum := add abc.value pp.value
  let out := copy sum.value
  ⟨out.value,aa.bitSteps+bb.bitSteps+cc.bitSteps+pp.bitSteps+na.bitSteps+ab.bitSteps+abc.bitSteps+sum.bitSteps+out.bitSteps,80⟩

theorem combine_view (a b c p : Cell) : view (combine a b c p).value=-view a-view b+view c+view p := by
  simp [combine]

theorem sum_magnitude (a b c p : ℤ) (A : ℕ)
    (ha : a.natAbs≤A) (hb : b.natAbs≤A) (hc : c.natAbs≤A) (hp : p.natAbs≤A) :
    (-a-b+c+p).natAbs≤4*A := by
  have hab := Int.natAbs_add_le (-a) (-b)
  have habc := Int.natAbs_add_le (-a-b) c
  have habcp := Int.natAbs_add_le (-a-b+c) p
  simp only [Int.natAbs_neg,← sub_eq_add_neg] at hab
  omega

theorem combine_magnitude (a b c p : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A)
    (hc : (view c).natAbs≤A) (hp : (view p).natAbs≤A) :
    (view (combine a b c p).value).natAbs≤4*A := by
  rw [combine_view]
  exact sum_magnitude _ _ _ _ A ha hb hc hp

theorem combine_bits (a b c p : Cell) (A : ℕ)
    (ha : (view a).natAbs≤A) (hb : (view b).natAbs≤A)
    (hc : (view c).natAbs≤A) (hp : (view p).natAbs≤A) :
    (combine a b c p).bitSteps≤9*BackendScalarBits.backendScalarUnit (4*A).size := by
  have wa : (view a).natAbs.size≤(4*A).size := Nat.size_le_size (ha.trans (by omega))
  have wb : (view b).natAbs.size≤(4*A).size := Nat.size_le_size (hb.trans (by omega))
  have wc : (view c).natAbs.size≤(4*A).size := Nat.size_le_size (hc.trans (by omega))
  have wp : (view p).natAbs.size≤(4*A).size := Nat.size_le_size (hp.trans (by omega))
  have hab : (-view a-view b).natAbs≤2*A := by
    have h := Int.natAbs_add_le (-view a) (-view b)
    simp only [Int.natAbs_neg,← sub_eq_add_neg] at h
    omega
  have habc : (-view a-view b+view c).natAbs≤3*A := by
    have h := Int.natAbs_add_le (-view a-view b) (view c)
    omega
  have hs := sum_magnitude _ _ _ _ A ha hb hc hp
  have h1 := copy_price (4*A).size a wa
  have h2 := copy_price (4*A).size b wb
  have h3 := copy_price (4*A).size c wc
  have h4 := copy_price (4*A).size p wp
  have h5 := sub_price (4*A).size zero (copy a).value (by simp) (by simpa using wa)
  have h6 := sub_price (4*A).size (neg (copy a).value).value (copy b).value (by simpa using wa) (by simpa using wb)
  have h7 := add_price (4*A).size (sub (neg (copy a).value).value (copy b).value).value (copy c).value
    (by simpa using Nat.size_le_size (hab.trans (by omega : 2*A≤4*A))) (by simpa using wc)
  have h8 := add_price (4*A).size (add (sub (neg (copy a).value).value (copy b).value).value (copy c).value).value (copy p).value
    (by simpa using Nat.size_le_size (habc.trans (by omega : 3*A≤4*A))) (by simpa using wp)
  have h9 := copy_price (4*A).size (add (add (sub (neg (copy a).value).value (copy b).value).value (copy c).value).value (copy p).value).value
    (by simpa using Nat.size_le_size hs)
  simp only [neg] at h6 h7 h8 h9
  simp only [combine,neg]
  omega

def mapBlock {F C : ℕ} (shape : Block F C) (f : Fin F → Fin C → Run Cell) : Run (Block F C) :=
  tabulate shape (fun d => tabulate (shape.get d) (f d))

@[simp] theorem mapBlock_get {F C : ℕ} (shape : Block F C) (f : Fin F → Fin C → Run Cell) (d : Fin F) (r : Fin C) :
    cellView (mapBlock shape f).value d r=view (f d r).value := by simp [mapBlock,cellView]

theorem mapBlock_bits {F C W : ℕ} (shape : Block F C) (f : Fin F → Fin C → Run Cell)
    (h : ∀ d r, (f d r).bitSteps≤W) : (mapBlock shape f).bitSteps≤F*(C*W) := by
  apply tabulate_bits
  intro d
  exact tabulate_bits _ _ (h d)

theorem mapBlock_control {F C W : ℕ} (shape : Block F C) (f : Fin F → Fin C → Run Cell)
    (h : ∀ d r, (f d r).control≤W) : (mapBlock shape f).control≤F*(C*(W+32)+40)+8 := by
  apply tabulate_control
  intro d
  exact tabulate_control _ _ (h d)

def previous {F C : ℕ} (a : Block F C) (d : Fin F) (r : Fin C) : Cell :=
  if h : 0<d.val then (a.get ⟨d.val-1,by omega⟩).get r else zero

def privateRow {F C : ℕ} (a b c : Block F C) : Run (Block F C) :=
  mapBlock a (fun d r =>
    let out := combine ((a.get d).get r) ((b.get d).get r) ((c.get d).get r) (previous c d r)
    ⟨out.value,out.bitSteps,out.control+4⟩)

theorem privateRow_view {F C : ℕ} (a b c : Block F C) (d : Fin F) (r : Fin C) :
    cellView (privateRow a b c).value d r =
      -cellView a d r-cellView b d r+cellView c d r+
      if h : 0<d.val then cellView c ⟨d.val-1,by omega⟩ r else 0 := by
  rw [privateRow,mapBlock_get,combine_view]
  unfold cellView previous
  split <;> rfl

theorem previous_magnitude {F C : ℕ} (a : Block F C) (A : ℕ) (ha : Bound A a) (d : Fin F) (r : Fin C) :
    (view (previous a d r)).natAbs≤A := by unfold previous; split; exact ha _ _; simp

theorem privateRow_magnitude {F C : ℕ} (a b c : Block F C) (A : ℕ)
    (ha : Bound A a) (hb : Bound A b) (hc : Bound A c) : Bound (4*A) (privateRow a b c).value := by
  intro d r
  simp only [privateRow,mapBlock_get]
  exact combine_magnitude _ _ _ _ A (ha d r) (hb d r) (hc d r) (previous_magnitude c A hc d r)

theorem privateRow_bits {F C : ℕ} (a b c : Block F C) (A : ℕ)
    (ha : Bound A a) (hb : Bound A b) (hc : Bound A c) :
    (privateRow a b c).bitSteps≤F*(C*(9*BackendScalarBits.backendScalarUnit (4*A).size)) := by
  apply mapBlock_bits
  intro d r
  exact combine_bits _ _ _ _ A (ha d r) (hb d r) (hc d r) (previous_magnitude c A hc d r)

theorem privateRow_control {F C : ℕ} (a b c : Block F C) :
    (privateRow a b c).control≤F*(C*116+40)+8 := mapBlock_control _ _ (fun _ _ => le_refl 84)

/-- Exact refinement of the shifted polynomial row on every retained degree
and residue. The only missing predecessor is the degree-zero coefficient. -/
theorem privateRow_extract {F q : ℕ} [NeZero q] (a b c : Block F q)
    (pa pb pc : Polynomial (CyclicRing.Cyclic q))
    (ha : ∀ d r, cellView a d r=(pa.coeff d.val) r)
    (hb : ∀ d r, cellView b d r=(pb.coeff d.val) r)
    (hc : ∀ d r, cellView c d r=(pc.coeff d.val) r) (d : Fin F) (r : Fin q) :
    cellView (privateRow a b c).value d r =
      ((-pa-pb+(1+Polynomial.X)*pc).coeff d.val) r := by
  rw [privateRow_view]
  rw [show (-pa-pb+(1+Polynomial.X)*pc)= -pa-pb+pc+Polynomial.X*pc by ring]
  simp only [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
    CyclicRing.add_coeff,ha,hb,hc]
  change _= -(pa.coeff d.val) r-(pb.coeff d.val) r+(pc.coeff d.val) r+((Polynomial.X*pc).coeff d.val) r
  split
  · rename_i hd
    rw [show d.val=(d.val-1)+1 by omega,Polynomial.coeff_X_mul]
    simp only [Nat.add_sub_cancel]
  · have hd : d.val=0 := by omega
    simp [hd]

#print axioms combine_view
#print axioms sum_magnitude
#print axioms combine_magnitude
#print axioms combine_bits
#print axioms mapBlock_get
#print axioms mapBlock_bits
#print axioms mapBlock_control
#print axioms privateRow_view
#print axioms previous_magnitude
#print axioms privateRow_magnitude
#print axioms privateRow_bits
#print axioms privateRow_control
#print axioms privateRow_extract
end ThinMatrix.BinaryResidualPolynomial
