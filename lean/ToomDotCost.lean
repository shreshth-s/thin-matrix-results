import ToomBitCost

/-!
# Bit costs of the concrete dot-product loop

The bounds below use the proved costs of the normalized signed-bit primitives.
They include the copied fixed weight, the input read, the multiplication,
the recursively accumulated tail, and the final addition. Tail magnitude
bounds are required for every actual suffix of the fixed incidence list.
-/

namespace ThinMatrix.ToomBitCost
open ThinMatrix.ToomCook

theorem int_product_size (x y : ℤ) (F B : ℕ)
    (hx : x.natAbs.size ≤ F) (hy : y.natAbs.size ≤ B) :
    (x*y).natAbs.size ≤ F+B := by
  apply Nat.size_le.mpr
  rw [Int.natAbs_mul, pow_add]
  exact (Nat.mul_le_mul_right y.natAbs (Nat.size_le.mp hx).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left
      (Nat.size_le.mp hy) (Nat.two_pow_pos F))

/-- Independent caps for fixed weights, input values, products, and tails. -/
theorem dotCounted_bit_cost {ι : Type*}
    (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ)
    (xs : List ι) (R F B P S : ℕ)
    (hw : ∀i∈xs,(weight i).natAbs.size≤F)
    (hr : ∀i∈xs,(read i).value.natAbs.size≤B)
    (hc : ∀i∈xs,(read i).operations≤R)
    (hp : ∀i∈xs,(weight i*(read i).value).natAbs.size≤P)
    (ht : ∀ys,ys<:+xs →
      (dotCounted bitPrimitives weight read ys).value.natAbs.size≤S) :
    (dotCounted bitPrimitives weight read xs).operations ≤
      xs.length*(R+(F+1)+60*(F+1)*(F+B+2)+4+
        50*(max P S+1))+1 := by
  induction xs with
  | nil => simp [dotCounted]
  | cons i is ih =>
    have hwi := hw i (by simp)
    have hri := hr i (by simp)
    have hci := hc i (by simp)
    have hti := ht is (List.suffix_cons i is)
    have hpi := hp i (by simp)
    have hm :
        (bitPrimitives.mul (weight i) (read i).value).operations ≤
          60*(F+1)*(F+B+2)+4 := by
      exact (bitPrimitive_mul_cost _ _).trans (by gcongr)
    have ha :
        (bitPrimitives.add (weight i*(read i).value)
          (dotCounted bitPrimitives weight read is).value).operations ≤
          50*(max P S+1) := by
      exact (bitPrimitive_add_cost _ _).trans (by gcongr)
    have hi := ih
      (fun j hj => hw j (by simp [hj]))
      (fun j hj => hr j (by simp [hj]))
      (fun j hj => hc j (by simp [hj]))
      (fun j hj => hp j (by simp [hj]))
      (fun ys hys => ht ys (hys.trans (List.suffix_cons i is)))
    simp only [dotCounted,Counted.bind,readConstant,
      bitPrimitives_correct.mul,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Product widths follow from the two input widths without an extra bit. -/
theorem dotCounted_bit_cost_from_operand_sizes {ι : Type*}
    (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ)
    (xs : List ι) (R F B S : ℕ)
    (hw : ∀i∈xs,(weight i).natAbs.size≤F)
    (hr : ∀i∈xs,(read i).value.natAbs.size≤B)
    (hc : ∀i∈xs,(read i).operations≤R)
    (ht : ∀ys,ys<:+xs →
      (dotCounted bitPrimitives weight read ys).value.natAbs.size≤S) :
    (dotCounted bitPrimitives weight read xs).operations ≤
      xs.length*(R+(F+1)+60*(F+1)*(F+B+2)+4+
        50*(max (F+B) S+1))+1 := by
  apply dotCounted_bit_cost weight read xs R F B (F+B) S hw hr hc
  · exact fun i hi=>int_product_size _ _ F B (hw i hi) (hr i hi)
  · exact ht

/-- A positive uniform register-width cap gives a quadratic local budget. -/
theorem dotCounted_bit_cost_uniform {ι : Type*}
    (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ)
    (xs : List ι) (R W : ℕ) (hW : 1≤W)
    (hw : ∀i∈xs,(weight i).natAbs.size≤W)
    (hr : ∀i∈xs,(read i).value.natAbs.size≤W)
    (hc : ∀i∈xs,(read i).operations≤R)
    (hp : ∀i∈xs,(weight i*(read i).value).natAbs.size≤W)
    (ht : ∀ys,ys<:+xs →
      (dotCounted bitPrimitives weight read ys).value.natAbs.size≤W) :
    (dotCounted bitPrimitives weight read xs).operations ≤
      xs.length*(R+150*(W+1)^2)+1 := by
  have h := dotCounted_bit_cost
    weight read xs R W W W W hw hr hc hp ht
  simp only [max_self] at h
  exact h.trans
    (Nat.add_le_add_right
      (Nat.mul_le_mul_left xs.length (by nlinarith)) 1)

#print axioms int_product_size
#print axioms dotCounted_bit_cost
#print axioms dotCounted_bit_cost_from_operand_sizes
#print axioms dotCounted_bit_cost_uniform

end ThinMatrix.ToomBitCost

namespace ThinMatrix.ToomBitCost

theorem tabulateInteger_operations_le (n F W I : ℕ)
    (f : Fin n → ToomCook.Counted ℤ)
    (hF : ∀ i, (f i).operations ≤ F)
    (hW : ∀ i, (f i).value.natAbs.size ≤ W)
    (hI : ∀ i : Fin n, i.val.size ≤ I) :
    (tabulateInteger n f).operations ≤ n*(F+W+I+3) := by
  rw [tabulateInteger_operations]
  calc
    (∑ i : Fin n,
        ((f i).operations+(f i).value.natAbs.size+i.val.size+1))+2*n ≤
        (∑ _i : Fin n, (F+W+I+1))+2*n := by
      apply Nat.add_le_add_right
      exact Finset.sum_le_sum (fun i _ => by
        have hfi:=hF i
        have hwi:=hW i
        have hii:=hI i
        omega)
    _ = n*(F+W+I+3) := by simp;ring

theorem tabulateCounted_operations_le {α : Type*} (n F : ℕ)
    (f : Fin n → ToomCook.Counted α)
    (hF : ∀ i, (f i).operations ≤ F) :
    (tabulateCounted n f).operations ≤ n*(F+2) := by
  rw [tabulateCounted_operations]
  calc
    (∑ i, (f i).operations)+2*n ≤ (∑ _i : Fin n, F)+2*n :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun i _=>hF i)) _
    _ = n*(F+2) := by simp;ring

/-- Finite register caps for one literal dot-product invocation. -/
structure DotCaps {ι : Type*}
    (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ)
    (xs : List ι) (R W : ℕ) : Prop where
  weight_width : ∀i∈xs,(weight i).natAbs.size≤W
  input : ∀i∈xs,(read i).value.natAbs.size≤W
  read_cost : ∀i∈xs,(read i).operations≤R
  product : ∀i∈xs,(weight i*(read i).value).natAbs.size≤W
  tail : ∀ys,ys<:+xs →
    (dotCounted bitPrimitives weight read ys).value.natAbs.size≤W

theorem DotCaps.operations {ι : Type*}
    {weight : ι→ℤ} {read : ι→ToomCook.Counted ℤ}
    {xs : List ι} {R W : ℕ}
    (h : DotCaps weight read xs R W) (hW : 1≤W) :
    (dotCounted bitPrimitives weight read xs).operations ≤
      xs.length*(R+150*(W+1)^2)+1 :=
  dotCounted_bit_cost_uniform weight read xs R W hW
    h.weight_width h.input h.read_cost h.product h.tail

theorem DotCaps.result {ι : Type*}
    {weight : ι→ℤ} {read : ι→ToomCook.Counted ℤ}
    {xs : List ι} {R W : ℕ}
    (h : DotCaps weight read xs R W) :
    (dotCounted bitPrimitives weight read xs).value.natAbs.size≤W :=
  h.tail xs List.suffix_rfl

theorem evaluateCounted_operations_le (k h R W : ℕ) (a : Array ℤ)
    (r : Fin (2*k-1)) (hW : 1≤W)
    (hDot : ∀j : Fin h,
      DotCaps (fun i : Fin k=>(r.val:ℤ)^i.val)
        (fun i=>indexedRead bitPrimitives a i.val h j.val)
        (List.ofFn (id : Fin k→Fin k)) R W)
    (hIndex : ∀j : Fin h,j.val.size≤W) :
    (evaluateCounted bitPrimitives k h a r).operations ≤
      h*(k*(R+150*(W+1)^2)+2*W+4) := by
  unfold evaluateCounted
  calc
    _ ≤ h*((k*(R+150*(W+1)^2)+1)+W+W+3) :=
      tabulateInteger_operations_le h _ W W _
        (fun j=>by simpa only [List.length_ofFn] using (hDot j).operations hW)
        (fun j=>(hDot j).result) hIndex
    _ = _ := by ring

theorem recombineCounted_operations_le (k h R W : ℕ)
    (parts : Array (Array ℤ)) (hW : 1≤W)
    (hDot : ∀j : Fin (2*k*h),
      DotCaps (fun _ : Fin (2*k-1)=>1)
        (fun d=>shiftedRead bitPrimitives parts d.val h j.val)
        (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))) R W)
    (hIndex : ∀j : Fin (2*k*h),j.val.size≤W) :
    (recombineCounted bitPrimitives k h parts).operations ≤
      (2*k*h)*((2*k-1)*(R+150*(W+1)^2)+2*W+4) := by
  unfold recombineCounted
  calc
    _ ≤ (2*k*h)*(((2*k-1)*(R+150*(W+1)^2)+1)+W+W+3) :=
      tabulateInteger_operations_le (2*k*h) _ W W _
        (fun j=>by simpa only [List.length_ofFn] using (hDot j).operations hW)
        (fun j=>(hDot j).result) hIndex
    _ = _ := by ring

#print axioms tabulateInteger_operations_le
#print axioms tabulateCounted_operations_le
#print axioms DotCaps.operations
#print axioms evaluateCounted_operations_le
#print axioms recombineCounted_operations_le

end ThinMatrix.ToomBitCost

namespace ThinMatrix.ToomBitCost
open ThinMatrix.ToomCook

theorem interpolateCounted_bit_cost_uniform (M h R W : ℕ)
    (children : Array (Array ℤ)) (hW : 1 ≤ W)
    (hc : ∀ (d : Fin M) (j : Fin (2*h)),
      DotCaps (integerWeight M d)
        (fun r : Fin M => readChild children r.val j.val)
        (List.ofFn (id : Fin M → Fin M)) R W)
    (hden : (commonDenominator M).size ≤ W)
    (hout : ∀ (d : Fin M) (j : Fin (2*h)),
      (bitPrimitives.divide (commonDenominator M)
        (dotCounted bitPrimitives (integerWeight M d)
          (fun r : Fin M => readChild children r.val j.val)
          (List.ofFn (id : Fin M → Fin M))).value).value.natAbs.size ≤ W)
    (hI : ∀ j : Fin (2*h), j.val.size ≤ W) :
    (interpolateCounted bitPrimitives M h children).operations ≤
      M*((2*h)*(M*(R+150*(W+1)^2)+80*(W+1)^2+2*W+8)+2) := by
  unfold interpolateCounted
  apply tabulateCounted_operations_le
  intro d
  apply (tabulateInteger_operations_le (2*h)
    (M*(R+150*(W+1)^2)+80*(W+1)^2+5) W W _ _ _ hI).trans
  · exact le_of_eq (by ring)
  · intro j
    have hd := (hc d j).operations hW
    have hv := (hc d j).result
    simp only [List.length_ofFn] at hd
    have hb : (bitPrimitives.divide (commonDenominator M)
        (dotCounted bitPrimitives (integerWeight M d)
          (fun r : Fin M => readChild children r.val j.val)
          (List.ofFn (id : Fin M → Fin M))).value).operations ≤
        80*(W+1)^2+4 := by
      exact (bitPrimitive_div_cost _ _).trans (by
        calc
          _ ≤ 40*(W+1)*(W+W+1)+4 := by gcongr
          _ ≤ _ := by nlinarith)
    dsimp only [Counted.bind]
    omega
  · exact hout d

#print axioms interpolateCounted_bit_cost_uniform

end ThinMatrix.ToomBitCost
