import BinaryRecursiveRecovery

set_option autoImplicit false

namespace ThinMatrix.BinaryRecursiveCost
open scoped BigOperators
open RecursiveTable (Layout Table read)
open RetainedEqualCopy (Base copies)
open BinaryCell BinaryRetainedBounds
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K] {r t : ℕ}

def height {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c Cell) : ℕ :=
  1+(∑ p,(view (read d.left p)).natAbs)+(∑ p,(view (read d.middle p)).natAbs)+
    (∑ p,(view (read d.right p)).natAbs)

theorem height_bounds {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c Cell) :
    Bounded d.left (height d) ∧ Bounded d.middle (height d) ∧ Bounded d.right (height d) := by
  have hl (p) := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin r×(Fin t×I)))) =>
    Nat.zero_le (view (read d.left i)).natAbs) (Finset.mem_univ p)
  have hm (p) := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin r×(Fin t×J)))) =>
    Nat.zero_le (view (read d.middle i)).natAbs) (Finset.mem_univ p)
  have hr (p) := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin r×(Fin t×K)))) =>
    Nat.zero_le (view (read d.right i)).natAbs) (Finset.mem_univ p)
  refine ⟨fun p => ?_,fun p => ?_,fun p => ?_⟩ <;> unfold height
  · have h := hl p;omega
  · have h := hm p;omega
  · have h := hr p;omega

def growth {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c Cell) : ℕ :=
  1+height d+t*a.size*height d+t*b.size*height d+r*height d

theorem growth_bounds {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c Cell) :
    1≤growth d ∧ height d≤growth d ∧ t*a.size*height d≤growth d ∧
      t*b.size*height d≤growth d ∧ r*height d≤growth d := by unfold growth;omega

def width {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) (k B : ℕ) : ℕ :=
  (4*k+1)*(growth (ClearedRecursiveBase.encode d).value).size+2*B.size+2+
    k*(ClearedRecursiveBase.common d^3).size+1

def bits {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c ℚ) (k B : ℕ) : ℕ :=
  (ClearedRecursiveBase.encode d).bitSteps+
    (BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)).bitSteps+
    (RetainedEqualCopyCosts.arithmetic r t a.size b.size c.size k+k)*BackendScalarBits.backendScalarUnit (width d k B)+
    t*c.size^k*(1024*(width d k B+1)^2)

/-- A closed resource bound for this particular recursive binary program.
Only original input magnitudes are premises; the base constants, coefficient
caps, intermediate widths and exact recovery charges are derived. -/
theorem execute_bits {a : Layout I} {b : Layout J} {c : Layout K} (ht : 0<t)
    (d : Base r t a b c ℚ) (k B : ℕ) (hB : 1≤B)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell)
    (hx : Bounded x B) (hy : Bounded y B) :
    (BinaryRecursiveRecovery.execute ht d k x y).bitSteps≤bits d k B := by
  let base := (ClearedRecursiveBase.encode d).value
  let F := growth base
  let H := height base
  let W := width d k B
  let denominator := BinaryMultiplierAdapter.encodeInteger ((ClearedRecursiveBase.common d:ℤ)^3)
  have hden : view denominator.value=((ClearedRecursiveBase.common d:ℤ)^3) :=
    BinaryMultiplierAdapter.encodeInteger_view _
  have hnat : (view denominator.value).natAbs=ClearedRecursiveBase.common d^3 := by
    rw [hden,Int.natAbs_pow,Int.natAbs_natCast]
  have hdpos : 1≤(view denominator.value).natAbs := by
    rw [hnat]
    exact one_le_pow₀ (FiniteRationalCoefficients.denominator_pos d.terms)
  have hdwidth : ((view denominator.value).natAbs^k).size≤W := by
    rw [hnat]
    exact (size_power _ k).trans (by dsimp [W,width];omega)
  have hf := growth_bounds base
  have hc := height_bounds base
  have hrun := run_bounds a b c ht base F H hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2
    hc.1 hc.2.1 hc.2.2 k B W hB ((bitCap_size F B k).trans (by dsimp [W,width,F,base];omega)) x y hx hy
  have hcap : cap F B k≤bitCap F B k := by
    unfold cap bitCap
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hf.1)
  have houtput (i) :
      (view (read (BinaryRetainedEqualCopy.run a b c ht base k x y).value i)).natAbs.size≤W :=
    (Nat.size_le_size ((hrun.1 i).trans hcap)).trans
      ((bitCap_size F B k).trans (by dsimp [W,width,F,base];omega))
  have hp := BinaryRecursiveRecovery.power_bits denominator.value k W hdpos hdwidth
  have hr := BinaryRecursiveRecovery.recover_bits (copies t c k)
    (BinaryRecursiveRecovery.power denominator.value k).value
    (BinaryRetainedEqualCopy.run a b c ht base k x y).value W
    (by simpa only [BinaryRecursiveRecovery.power_view,Int.natAbs_pow] using hdwidth) houtput
  rw [show (copies t c k).size=t*c.size^k by
    simp [copies,RecursiveTable.prod,RecursiveTable.fin]] at hr
  have hsum := Nat.add_le_add (Nat.add_le_add hp hrun.2) hr
  simp only [BinaryRecursiveRecovery.execute,bits]
  dsimp only [base,denominator,W] at hsum
  nlinarith

#print axioms height_bounds
#print axioms growth_bounds
#print axioms execute_bits
end ThinMatrix.BinaryRecursiveCost
