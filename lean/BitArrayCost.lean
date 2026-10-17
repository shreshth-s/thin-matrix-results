import BitArraySimulation
import ToomExecutionBound

/-!
# Cost refinement for actual signed-bit coefficient arrays

The actual bit program reuses canonical registers. Integer array views are
specifications only. Relative counter bounds charge the additional binary
index generation and copies against the native counter's existing actual
operand, output, and address bit charges. No coefficient-width premise is
introduced by this refinement.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace ThinMatrix.BitArraySimulation
open scoped BigOperators
open ToomCook

 theorem dot_denote_native {ι : Type*} (weight : ι→Signed) (read : ι→ToomCook.Counted Signed)
    (native : ι→ToomCook.Counted ℤ) (hv : ∀i,denote (read i).value=(native i).value) (xs : List ι) :
    denote (dot weight read xs).value =
      (ToomBitCost.dotCounted ToomBitCost.bitPrimitives (fun i=>denote (weight i)) native xs).value := by
  rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hv]

 theorem dot_cost_refinement {ι : Type*} (R : ℕ) (hR : 4≤R)
    (weight : ι→Signed) (read : ι→ToomCook.Counted Signed) (native : ι→ToomCook.Counted ℤ)
    (hv : ∀i,denote (read i).value=(native i).value)
    (hc : ∀i,(read i).operations≤R*(native i).operations) (xs : List ι) :
    (dot weight read xs).operations ≤ R*
      (ToomBitCost.dotCounted ToomBitCost.bitPrimitives (fun i=>denote (weight i)) native xs).operations := by
  induction xs with
  | nil => simpa only [dot,ToomBitCost.dotCounted,Nat.mul_one] using hR.trans' (by decide : 1≤4)
  | cons i xs ih =>
    have hw := (readConstant_cost (weight i)).trans (Nat.mul_le_mul_right _ hR)
    have hm := mul_cost (readConstant (weight i)).value (read i).value
    simp only [readConstant_value,hv] at hm
    have hm' := hm.le.trans (Nat.le_mul_of_pos_left _ (by omega : 0<R))
    have ha := add_cost
      (mul (readConstant (weight i)).value (read i).value).value (dot weight read xs).value
    simp only [mul_value,readConstant_value,hv,dot_denote_native weight read native hv xs] at ha
    have ha' := ha.le.trans (Nat.le_mul_of_pos_left _ (by omega : 0<R))
    have hr := hc i
    simp only [dot,bind,ToomBitCost.dotCounted,ToomBitCost.Counted.bind,
      ToomBitCost.readConstant,ToomBitCost.bitPrimitives_correct.mul,readConstant_value]
    simp only [ToomBitCost.readConstant] at hw
    nlinarith

 theorem indexedRead_cost_refinement (a : Array Signed) (i h j : ℕ)
    (iBits hBits jBits : Signed) (hi : denote iBits=(i:ℤ))
    (hh : denote hBits=(h:ℤ)) (hj : denote jBits=(j:ℤ)) :
    (indexedRead a iBits hBits jBits).operations ≤
      8*(ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i h j).operations := by
  let address := (add (mul iBits hBits).value jBits).value
  have ha : denote address=((i*h+j:ℕ):ℤ) := by
    dsimp only [address]
    rw [add_value,mul_value,hi,hh,hj]
    push_cast
    ring
  have hd : (decodeAddress address.val.magnitude).value=i*h+j := by
    rw [decodeMagnitude_value,ha,Int.natAbs_natCast]
  have hdc : (decodeAddress address.val.magnitude).operations=5*(i*h+j).size+1 := by
    rw [decodeAddress_cost,magnitude_length,ha,Int.natAbs_natCast]
  have hr := readInteger_cost a (i*h+j)
  have hm := mul_cost iBits hBits
  have hs := add_cost (mul iBits hBits).value jBits
  rw [hi,hh] at hm
  rw [mul_value,hi,hh,hj] at hs
  have hread : (i*h+j).size+1 ≤ (ToomBitCost.readInteger (arrayView a) (i*h+j)).operations := by
    simp only [ToomBitCost.readInteger]
    omega
  simp only [indexedRead,bind]
  change (mul iBits hBits).operations+((add (mul iBits hBits).value jBits).operations+
    ((decodeAddress address.val.magnitude).operations+
      (readInteger a (decodeAddress address.val.magnitude).value).operations)) ≤ _
  rw [hd,hdc,hm,hs]
  simp only [ToomBitCost.indexedRead,ToomBitCost.Counted.bind,
    ToomBitCost.bitPrimitives_correct.mul,ToomBitCost.bitPrimitives_correct.add,
    ←Nat.cast_mul,←Nat.cast_add,Int.natAbs_natCast]
  nlinarith

 theorem indexedRead_native_pos (a : Array ℤ) (i h j : ℕ) :
    1 ≤ (ToomBitCost.indexedRead ToomBitCost.bitPrimitives a i h j).operations := by
  simp only [ToomBitCost.indexedRead,ToomBitCost.Counted.bind,ToomBitCost.readInteger]
  omega

theorem shiftedRead_cost_refinement (parts : Array (Array Signed)) (d h j : ℕ)
    (dBits hBits jBits : Signed) (hd : denote dBits=(d:ℤ))
    (hh : denote hBits=(h:ℤ)) (hj : denote jBits=(j:ℤ)) :
    (shiftedRead parts d dBits hBits jBits).operations ≤
      16*(ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d h j).operations := by
  let address := (add jBits (negate (mul hBits dBits).value).value).value
  let z : ℤ := (j:ℤ)-((h*d:ℕ):ℤ)
  have ha : denote address=z := by
    dsimp only [address,z]
    rw [add_value,negate_value,mul_value,hh,hd,hj]
    push_cast
    ring
  have hdec : (decodeAddress address.val.magnitude).value=z.natAbs := by
    rw [decodeMagnitude_value,ha]
  have hdc : (decodeAddress address.val.magnitude).operations=5*z.natAbs.size+1 := by
    rw [decodeAddress_cost,magnitude_length,ha]
  have hm := mul_cost hBits dBits
  have hs := add_cost jBits (negate (mul hBits dBits).value).value
  rw [hh,hd] at hm
  rw [hj,negate_value,mul_value,hh,hd] at hs
  have hr := readChild_cost parts d z.natAbs
  have hn : (negate (mul hBits dBits).value).operations=4 := negate_cost _
  have he : (j:ℤ)+-((h:ℤ)*(d:ℤ))=z := by dsimp [z];ring
  simp only [shiftedRead,bind]
  change (mul hBits dBits).operations+((negate (mul hBits dBits).value).operations+
    ((add jBits (negate (mul hBits dBits).value).value).operations+
    ((if address.val.negative then (⟨zero,2⟩ : ToomCook.Counted Signed) else
      ⟨(readChild parts d (decodeAddress address.val.magnitude).value).value,
       (decodeAddress address.val.magnitude).operations+
         (readChild parts d (decodeAddress address.val.magnitude).value).operations+2⟩)).operations)) ≤ _
  rw [hm,hs,hn]
  simp only [ToomBitCost.shiftedRead,ToomBitCost.Counted.bind,
    ToomBitCost.bitPrimitives_correct.mul,ToomBitCost.bitPrimitives_correct.add,he]
  by_cases hz : 0≤z
  · have hb : address.val.negative=false := (negative_false address).mpr (by rw [ha];exact hz)
    simp only [hb,Bool.false_eq_true,if_false,if_pos hz,hdec,hdc]
    nlinarith
  · have hb : address.val.negative=true := (negative_true address).mpr (by rw [ha];omega)
    simp only [hb,if_true,if_neg hz]
    omega

theorem shiftedRead_native_pos (parts : Array (Array ℤ)) (d h j : ℕ) :
    1 ≤ (ToomBitCost.shiftedRead ToomBitCost.bitPrimitives parts d h j).operations := by
  simp only [ToomBitCost.shiftedRead,ToomBitCost.Counted.bind]
  omega

theorem tabulate_cost_refinement {α β : Type*} (R n : ℕ) (hR : 1≤R)
    (f : Fin n→ToomCook.Counted α) (g : Fin n→ToomCook.Counted β)
    (hc : ∀i,(f i).operations≤R*(g i).operations) :
    (tabulate n f).operations ≤ R*(ToomBitCost.tabulateCounted n g).operations := by
  rw [tabulate_operations,ToomBitCost.tabulateCounted_operations]
  have hsum : (∑i,(f i).operations) ≤ R*(∑i,(g i).operations) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>hc i)
  have halloc : 2*n≤R*(2*n) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

theorem tabulateInteger_operations_refinement (n : ℕ)
    (f : Fin n → Signed → ToomCook.Counted Signed) :
    (tabulateInteger n f).operations = (indices n).operations+
      (Finset.univ.sum (fun i : Fin n => (f i ((indices n).value.get i)).operations+
        2*(denote (f i ((indices n).value.get i)).value).natAbs.size+i.val.size+4))+2*n := by
  simp only [tabulateInteger,tabulate_operations,bind,copy_cost,Nat.add_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  omega

theorem tabulateInteger_cost_refinement (n W C : ℕ)
    (hn : 1 ≤ n) (hW : n.size ≤ W) (hC : 100*(W+2) ≤ C)
    (f : Fin n → Signed → ToomCook.Counted Signed) (g : Fin n → ToomCook.Counted ℤ)
    (hv : ∀ i, denote (f i ((indices n).value.get i)).value=(g i).value)
    (hc : ∀ i, (f i ((indices n).value.get i)).operations ≤ C*(g i).operations) :
    (tabulateInteger n f).operations ≤ C*(ToomBitCost.tabulateInteger n g).operations := by
  have hCp : 4 ≤ C := by omega
  have hpoint : ∀ i : Fin n,
      (f i ((indices n).value.get i)).operations+
        2*(denote (f i ((indices n).value.get i)).value).natAbs.size+i.val.size+4 ≤
      C*((g i).operations+(g i).value.natAbs.size+i.val.size+1) := by
    intro i
    rw [hv i]
    have hb := hc i
    have hs := Nat.mul_le_mul_right (g i).value.natAbs.size (show 2 ≤ C by omega)
    have hi := Nat.mul_le_mul_right i.val.size (show 1 ≤ C by omega)
    nlinarith
  have hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => hpoint i)
  have hindex := indices_cost n
  have hm := Nat.mul_le_mul_left (70*n) (Nat.add_le_add_right hW 2)
  have hcn := Nat.mul_le_mul_right (2*n) hC
  have ho : (indices n).operations+2*n ≤ C*(2*n) := by nlinarith
  rw [tabulateInteger_operations_refinement,ToomBitCost.tabulateInteger_operations]
  rw [← Finset.mul_sum] at hsum
  nlinarith

theorem power_native_size (k s : ℕ) :
    (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).value.natAbs.size ≤
      (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations := by
  cases s with
  | zero => simp [ToomBitCost.powerCounted]
  | succ s =>
    simp only [ToomBitCost.powerCounted,ToomBitCost.Counted.bind]
    omega

theorem power_native_pos (k s : ℕ) :
    1 ≤ (ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations := by
  cases s with
  | zero => rfl
  | succ s =>
    simp only [ToomBitCost.powerCounted,ToomBitCost.Counted.bind,ToomBitCost.readConstant]
    omega

theorem power_cost_refinement (k : ℕ) (rom : ROM k) (s : ℕ) :
    (power k rom s).operations ≤ 4*(ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations := by
  induction s with
  | zero => change (1:ℕ)≤4;omega
  | succ s ih =>
    have hb := readConstant_cost rom.base
    rw [rom.base_value] at hb
    have hm := mul_cost (readConstant rom.base).value (power k rom s).value
    rw [readConstant_value,rom.base_value,power_value] at hm
    have hc := copy_cost (mul (readConstant rom.base).value (power k rom s).value).value
    rw [mul_value,readConstant_value,rom.base_value,power_value] at hc
    simp only [power,bind,ToomBitCost.powerCounted,ToomBitCost.Counted.bind,
      ToomBitCost.powerCounted_value _ ToomBitCost.bitPrimitives_correct,
      ToomBitCost.readConstant,ToomBitCost.bitPrimitives_correct.mul,readConstant_value]
    simp only [ToomBitCost.readConstant] at hb
    rw [hc,hm]
    nlinarith

theorem power_decode_cost_refinement (k : ℕ) (rom : ROM k) (s : ℕ) :
    (power k rom s).operations+(decodeAddress (power k rom s).value.val.magnitude).operations ≤
      10*(ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations := by
  have hp := power_cost_refinement k rom s
  have hs := power_native_size k s
  have hn := power_native_pos k s
  rw [ToomBitCost.powerCounted_value _ ToomBitCost.bitPrimitives_correct] at hs
  simp only [decodeAddress_cost,magnitude_length,power_value]
  nlinarith

theorem interpolate_cost_refinement (k h W C : ℕ) (rom : ROM k)
    (children : Array (Array Signed)) (hh : 1≤h) (hW : (2*h).size≤W)
    (hC : 100*(W+2)≤C) :
    (interpolate k h rom children).operations ≤ C*
      (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) h
        (childrenView children)).operations := by
  unfold interpolate ToomBitCost.interpolateCounted
  apply tabulate_cost_refinement C (2*k-1) (by omega)
  intro d
  let weight : Fin (2*k-1)→Signed := fun r=>(rom.interpolation.get d).get r
  let read (j : Fin (2*h)) : Fin (2*k-1)→ToomCook.Counted Signed := fun r=>readChild children r.val j.val
  let native (j : Fin (2*h)) : Fin (2*k-1)→ToomCook.Counted ℤ :=
    fun r=>ToomBitCost.readChild (childrenView children) r.val j.val
  let bitdot (j : Fin (2*h)) := dot weight (read j) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
  let natdot (j : Fin (2*h)) := ToomBitCost.dotCounted ToomBitCost.bitPrimitives
    (ToomCook.integerWeight (2*k-1) d) (native j) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
  have hvread (j : Fin (2*h)) (r : Fin (2*k-1)) : denote (read j r).value=(native j r).value :=
    readChild_value children r.val j.val
  have hcread (j : Fin (2*h)) (r : Fin (2*k-1)) : (read j r).operations≤C*(native j r).operations :=
    (readChild_cost children r.val j.val).trans (Nat.mul_le_mul_right _ (by omega : 3≤C))
  have hvdot (j : Fin (2*h)) : denote (bitdot j).value=(natdot j).value := by
    have hx := dot_denote_native weight (read j) (native j) (hvread j)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
    simpa only [bitdot,natdot,weight,rom.interpolation_value] using hx
  have hcdot (j : Fin (2*h)) : (bitdot j).operations≤C*(natdot j).operations := by
    have hx := dot_cost_refinement C (by omega) weight (read j) (native j)
      (hvread j) (hcread j) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
    simpa only [bitdot,natdot,weight,rom.interpolation_value] using hx
  change (tabulateInteger (2*h) (fun j _=>bind (bitdot j) (divide rom.divisor))).operations ≤
    C*(ToomBitCost.tabulateInteger (2*h) (fun j=>ToomBitCost.Counted.bind (natdot j)
      (ToomBitCost.bitPrimitives.divide (ToomCook.commonDenominator (2*k-1))))).operations
  apply tabulateInteger_cost_refinement (2*h) W C (by omega) hW hC
  · intro j
    simp only [bind,ToomBitCost.Counted.bind]
    rw [divide_value _ _ _ rom.divisor_value,hvdot]
  · intro j
    have hd := divide_cost (ToomCook.commonDenominator (2*k-1)) (bitdot j).value
      rom.divisor rom.divisor_value
    rw [hvdot] at hd
    have hd' := hd.trans (Nat.mul_le_mul_right _ (by omega : 2≤C))
    have hx := hcdot j
    simp only [bind,ToomBitCost.Counted.bind]
    nlinarith

 theorem recombine_kernel_cost_refinement (k h : ℕ) (rom : ROM k)
    (hBits : Signed) (hh : denote hBits=(h:ℤ)) (parts : Array (Array Signed))
    (j : Fin (2*k*h)) (jBits : Signed) (hj : denote jBits=(j.val:ℤ)) :
    (dot (fun _ : Fin (2*k-1)=>one)
      (fun d=>let value:=shiftedRead parts d.val (rom.indexM.get d) hBits jBits
        ⟨value.value,value.operations+1⟩)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))).operations ≤
    17*(ToomBitCost.dotCounted ToomBitCost.bitPrimitives
      (fun _ : Fin (2*k-1)=>(1:ℤ))
      (fun d=>ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d.val h j.val)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))).operations := by
  have hv : ∀d : Fin (2*k-1),
      denote (show Counted Signed from
        let value:=shiftedRead parts d.val (rom.indexM.get d) hBits jBits
        ⟨value.value,value.operations+1⟩).value=
      (ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d.val h j.val).value := by
    intro d
    exact shiftedRead_value parts d.val h j.val _ _ _ (rom.indexM_value d) hh hj
  have hc : ∀d : Fin (2*k-1),
      (show Counted Signed from
        let value:=shiftedRead parts d.val (rom.indexM.get d) hBits jBits
        ⟨value.value,value.operations+1⟩).operations≤
      17*(ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d.val h j.val).operations := by
    intro d
    have hcost:=shiftedRead_cost_refinement parts d.val h j.val _ _ _ (rom.indexM_value d) hh hj
    have hpos:=shiftedRead_native_pos (childrenView parts) d.val h j.val
    dsimp only
    nlinarith
  simpa only [denote_one] using
    dot_cost_refinement 17 (by decide) (fun _ : Fin (2*k-1)=>one)
      (fun d=>let value:=shiftedRead parts d.val (rom.indexM.get d) hBits jBits
        ⟨value.value,value.operations+1⟩)
      (fun d=>ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d.val h j.val)
      hv hc (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))

 theorem recombine_cost_refinement (k h W C : ℕ) (hn : 1 ≤ 2*k*h)
    (hW : (2*k*h).size ≤ W) (hC : 100*(W+2) ≤ C)
    (rom : ROM k) (hBits : Signed) (hh : denote hBits=(h:ℤ))
    (parts : Array (Array Signed)) :
    (recombine k h rom hBits parts).operations ≤
      C*(ToomBitCost.recombineCounted ToomBitCost.bitPrimitives k h (childrenView parts)).operations := by
  unfold recombine ToomBitCost.recombineCounted
  apply tabulateInteger_cost_refinement (2*k*h) W C hn hW hC
  · intro j
    rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d _
    simp only [denote_one]
    congr 1
    exact shiftedRead_value parts d.val h j.val _ _ _ (rom.indexM_value d) hh
      (indices_value (2*k*h) j)
  · intro j
    have hk:=recombine_kernel_cost_refinement k h rom hBits hh parts j _
      (indices_value (2*k*h) j)
    exact hk.trans (Nat.mul_le_mul_right _ (by omega : 17≤C))

namespace ExecuteDecomp

def left (k : ℕ) (rom : ROM k) (s : ℕ) (a : Array Signed) :=
  tabulate (2*k-1) (fun r => evaluate k (k^s) rom (power k rom s).value a r)

def children (k : ℕ) (rom : ROM k) (s : ℕ) (a b : Array Signed) :=
  tabulate (2*k-1) (fun r =>
    bind (readChildArray (left k rom s a).value r.val) (fun la =>
      bind (readChildArray (left k rom s b).value r.val) (execute k rom s la)))

noncomputable def nativeLeft (k s : ℕ) (a : Array ℤ) :=
  ToomBitCost.tabulateCounted (2*k-1) (fun r =>
    ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k (k^s) a r)

noncomputable def nativeChildren (k s : ℕ) (a b : Array ℤ) :=
  ToomBitCost.tabulateCounted (2*k-1) (fun r =>
    ToomBitCost.Counted.bind (ToomBitCost.readChildArray (nativeLeft k s a).value r.val)
      (fun la => ToomBitCost.Counted.bind
        (ToomBitCost.readChildArray (nativeLeft k s b).value r.val)
        (ToomBitCost.execute ToomBitCost.bitPrimitives k s la)))

theorem left_view (k : ℕ) (rom : ROM k) (s : ℕ) (a : Array Signed) :
    childrenView (left k rom s a).value = (nativeLeft k s (arrayView a)).value := by
  exact evaluateTable_view k (k^s) rom _ (power_value k rom s) a

theorem children_view (k : ℕ) (rom : ROM k) (s : ℕ) (a b : Array Signed) :
    childrenView (children k rom s a b).value =
      (nativeChildren k s (arrayView a) (arrayView b)).value := by
  simp only [children,nativeChildren,tabulate_value,ToomBitCost.tabulateCounted_value,
    bind,ToomBitCost.Counted.bind,childrenView,Array.map_ofFn]
  apply congrArg Array.ofFn
  funext r
  simp only [Function.comp_apply]
  rw [execute_value]
  simp only [readChildArray_value]
  rw [left_view,left_view]

theorem bit_succ_operations (k : ℕ) (rom : ROM k) (s : ℕ) (a b : Array Signed) :
    (execute k rom (s+1) a b).operations =
      (s+1).size+1+(power k rom s).operations+
      (decodeAddress (power k rom s).value.val.magnitude).operations+
      (left k rom s a).operations+(left k rom s b).operations+
      (∑r : Fin (2*k-1), (
        (readChildArray (left k rom s a).value r.val).operations+
        (readChildArray (left k rom s b).value r.val).operations+
        (execute k rom s (readChildArray (left k rom s a).value r.val).value
          (readChildArray (left k rom s b).value r.val).value).operations))+2*(2*k-1)+
      (interpolate k (k^s) rom (children k rom s a b).value).operations+
      (recombine k (k^s) rom (power k rom s).value
        (interpolate k (k^s) rom (children k rom s a b).value).value).operations := by
  simp only [execute,bind,decode_power]
  simp only [left,children,tabulate_operations,bind]
  ac_rfl

theorem native_succ_operations (k s : ℕ) (a b : Array ℤ) :
    (ToomBitCost.execute ToomBitCost.bitPrimitives k (s+1) a b).operations =
      (s+1).size+1+(ToomBitCost.powerCounted ToomBitCost.bitPrimitives k s).operations+
      (nativeLeft k s a).operations+(nativeLeft k s b).operations+
      (∑r : Fin (2*k-1), (
        (ToomBitCost.readChildArray (nativeLeft k s a).value r.val).operations+
        (ToomBitCost.readChildArray (nativeLeft k s b).value r.val).operations+
        (ToomBitCost.execute ToomBitCost.bitPrimitives k s
          (ToomBitCost.readChildArray (nativeLeft k s a).value r.val).value
          (ToomBitCost.readChildArray (nativeLeft k s b).value r.val).value).operations))+2*(2*k-1)+
      (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) (k^s)
        (nativeChildren k s a b).value).operations+
      (ToomBitCost.recombineCounted ToomBitCost.bitPrimitives k (k^s)
        (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) (k^s)
          (nativeChildren k s a b).value).value).operations := by
  simp only [ToomBitCost.execute,ToomBitCost.Counted.bind,
    ToomBitCost.powerCounted_value _ ToomBitCost.bitPrimitives_correct,
    Int.natAbs_natCast]
  simp only [nativeLeft,nativeChildren,ToomBitCost.tabulateCounted_operations,
    ToomBitCost.Counted.bind]
  ac_rfl


end ExecuteDecomp

theorem evaluate_kernel_cost_refinement (k h : ℕ) (rom : ROM k)
    (hBits : Signed) (hh : denote hBits=(h:ℤ)) (a : Array Signed)
    (r : Fin (2*k-1)) (j : Fin h) (jBits : Signed) (hj : denote jBits=(j.val:ℤ)) :
    (dot (fun i : Fin k=>(rom.evaluation.get r).get i)
      (fun i=>let value:=indexedRead a (rom.indexK.get i) hBits jBits
        ⟨value.value,value.operations+1⟩)
      (List.ofFn (id : Fin k→Fin k))).operations ≤
    9*(ToomBitCost.dotCounted ToomBitCost.bitPrimitives
      (fun i : Fin k=>(r.val:ℤ)^i.val)
      (fun i=>ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i.val h j.val)
      (List.ofFn (id : Fin k→Fin k))).operations := by
  have hv : ∀i : Fin k,
      denote (show Counted Signed from
        let value:=indexedRead a (rom.indexK.get i) hBits jBits
        ⟨value.value,value.operations+1⟩).value=
      (ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i.val h j.val).value := by
    intro i
    dsimp only
    exact indexedRead_value a i.val h j.val (rom.indexK.get i) hBits jBits (rom.indexK_value i) hh hj
  have hc : ∀i : Fin k,
      (show Counted Signed from
        let value:=indexedRead a (rom.indexK.get i) hBits jBits
        ⟨value.value,value.operations+1⟩).operations≤
      9*(ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i.val h j.val).operations := by
    intro i
    have hcost:=indexedRead_cost_refinement a i.val h j.val (rom.indexK.get i) hBits jBits (rom.indexK_value i) hh hj
    have hpos:=indexedRead_native_pos (arrayView a) i.val h j.val
    dsimp only
    nlinarith
  have hd := dot_cost_refinement 9 (by decide)
      (fun i : Fin k=>(rom.evaluation.get r).get i)
      (fun i=>let value:=indexedRead a (rom.indexK.get i) hBits jBits
        ⟨value.value,value.operations+1⟩)
      (fun i=>ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i.val h j.val)
      hv hc (List.ofFn (id : Fin k→Fin k))
  have hw : (fun i : Fin k => denote ((rom.evaluation.get r).get i)) =
      (fun i : Fin k => (r.val:ℤ)^i.val) := by
    funext i
    exact rom.evaluation_value r i
  rw [hw] at hd
  exact hd

theorem evaluate_cost_refinement (k h W C : ℕ) (hn : 1 ≤ h)
    (hW : h.size ≤ W) (hC : 100*(W+2) ≤ C)
    (rom : ROM k) (hBits : Signed) (hh : denote hBits=(h:ℤ))
    (a : Array Signed) (r : Fin (2*k-1)) :
    (evaluate k h rom hBits a r).operations ≤
      C*(ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h (arrayView a) r).operations := by
  unfold evaluate ToomBitCost.evaluateCounted
  apply tabulateInteger_cost_refinement h W C hn hW hC
  · intro j
    rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    rw [rom.evaluation_value]
    congr 1
    dsimp only
    exact indexedRead_value a i.val h j.val (rom.indexK.get i) hBits ((indices h).value.get j) (rom.indexK_value i) hh (indices_value h j)
  · intro j
    have hk:=evaluate_kernel_cost_refinement k h rom hBits hh a r j _ (indices_value h j)
    exact hk.trans (Nat.mul_le_mul_right _ (by omega : 9≤C))


theorem execute_zero_cost_refinement (k W C : ℕ) (rom : ROM k)
    (a b : Array Signed) (hW : (2 : ℕ).size ≤ W) (hC : 100*(W+2) ≤ C) :
    (execute k rom 0 a b).operations ≤
      C*(ToomBitCost.execute ToomBitCost.bitPrimitives k 0 (arrayView a) (arrayView b)).operations := by
  have hCp : 3 ≤ C := by omega
  let z := (mul (readInteger a 0).value (readInteger b 0).value).value
  let zn := (ToomBitCost.bitPrimitives.mul
    (ToomBitCost.readInteger (arrayView a) 0).value
    (ToomBitCost.readInteger (arrayView b) 0).value).value
  let f : Fin 2 → Signed → Counted Signed :=
    fun j _ => if j.val=0 then ⟨z,1⟩ else ⟨zero,1⟩
  let g : Fin 2 → Counted ℤ := fun j => if j.val=0 then ⟨zn,1⟩ else ⟨0,1⟩
  have hz : denote z = zn := by
    dsimp [z,zn]
    rw [mul_value,readInteger_value,readInteger_value,ToomBitCost.bitPrimitives_correct.mul]
  have ht := tabulateInteger_cost_refinement 2 W C (by omega) hW hC f g
    (by intro i; dsimp [f,g]; split_ifs <;> simp only [hz,denote_zero])
    (by intro i; dsimp [f,g]; split_ifs <;> simpa using (show 1 ≤ C by omega))
  have hr1 := (readInteger_cost a 0).trans (Nat.mul_le_mul_right _ hCp)
  have hr2 := (readInteger_cost b 0).trans (Nat.mul_le_mul_right _ hCp)
  have hm := mul_cost (readInteger a 0).value (readInteger b 0).value
  rw [readInteger_value,readInteger_value] at hm
  have hm' := hm.le.trans (Nat.le_mul_of_pos_left _ (by omega : 0<C))
  simp only [execute,bind,ToomBitCost.execute,ToomBitCost.Counted.bind]
  change 1+((readInteger a 0).operations+((readInteger b 0).operations+
    ((mul (readInteger a 0).value (readInteger b 0).value).operations+
      (tabulateInteger 2 f).operations))) ≤ _
  change _ ≤ C*(1+((ToomBitCost.readInteger (arrayView a) 0).operations+
    ((ToomBitCost.readInteger (arrayView b) 0).operations+
    ((ToomBitCost.bitPrimitives.mul
      (ToomBitCost.readInteger (arrayView a) 0).value
      (ToomBitCost.readInteger (arrayView b) 0).value).operations+
        (ToomBitCost.tabulateInteger 2 g).operations))))
  nlinarith


theorem execute_step_cost_refinement (k s W C : ℕ) (hk : 2≤k) (hC : 100*(W+2)≤C)
    (hhBits : (k^s).size≤W) (h2Bits : (2*k^s).size≤W) (hfullBits : (2*k*k^s).size≤W)
    (rom : ROM k) (a b : Array Signed)
    (hchild : ∀ a b : Array Signed, (execute k rom s a b).operations ≤
      C*(ToomBitCost.execute ToomBitCost.bitPrimitives k s (arrayView a) (arrayView b)).operations) :
    (execute k rom (s+1) a b).operations ≤
      C*(ToomBitCost.execute ToomBitCost.bitPrimitives k (s+1) (arrayView a) (arrayView b)).operations := by
  have hh : 1≤k^s := Nat.one_le_pow _ _ (by omega)
  have hp := power_value k rom s
  have hleft (a : Array Signed) : (ExecuteDecomp.left k rom s a).operations ≤
      C*(ExecuteDecomp.nativeLeft k s (arrayView a)).operations := by
    apply tabulate_cost_refinement C (2*k-1) (by omega)
    intro r
    exact evaluate_cost_refinement k (k^s) W C hh hhBits hC rom _ hp a r
  have hleftA := hleft a
  have hleftB := hleft b
  have hpoint (r : Fin (2*k-1)) :
      (readChildArray (ExecuteDecomp.left k rom s a).value r.val).operations+
        (readChildArray (ExecuteDecomp.left k rom s b).value r.val).operations+
        (execute k rom s (readChildArray (ExecuteDecomp.left k rom s a).value r.val).value
          (readChildArray (ExecuteDecomp.left k rom s b).value r.val).value).operations ≤
      C*((ToomBitCost.readChildArray (ExecuteDecomp.nativeLeft k s (arrayView a)).value r.val).operations+
        (ToomBitCost.readChildArray (ExecuteDecomp.nativeLeft k s (arrayView b)).value r.val).operations+
        (ToomBitCost.execute ToomBitCost.bitPrimitives k s
          (ToomBitCost.readChildArray (ExecuteDecomp.nativeLeft k s (arrayView a)).value r.val).value
          (ToomBitCost.readChildArray (ExecuteDecomp.nativeLeft k s (arrayView b)).value r.val).value).operations) := by
    have hr := hchild (readChildArray (ExecuteDecomp.left k rom s a).value r.val).value
      (readChildArray (ExecuteDecomp.left k rom s b).value r.val).value
    rw [readChildArray_value,readChildArray_value,ExecuteDecomp.left_view,ExecuteDecomp.left_view] at hr
    have hi : r.val.size+1≤C*(r.val.size+1) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [readChildArray,ToomBitCost.readChildArray] at hr ⊢
    nlinarith
  have hsum := Finset.sum_le_sum (fun (r : Fin (2*k-1)) (_ : r∈Finset.univ)=>hpoint r)
  rw [←Finset.mul_sum] at hsum
  have hI := interpolate_cost_refinement k (k^s) W C rom
    (ExecuteDecomp.children k rom s a b).value hh h2Bits hC
  rw [ExecuteDecomp.children_view] at hI
  have hR := recombine_cost_refinement k (k^s) W C (by nlinarith) hfullBits hC rom
    (power k rom s).value hp (interpolate k (k^s) rom (ExecuteDecomp.children k rom s a b).value).value
  rw [interpolate_value,ExecuteDecomp.children_view] at hR
  have hP := (power_decode_cost_refinement k rom s).trans (Nat.mul_le_mul_right _ (by omega : 10≤C))
  have hcontrol : (s+1).size+1≤C*((s+1).size+1) := Nat.le_mul_of_pos_left _ (by omega)
  have halloc : 2*(2*k-1)≤C*(2*(2*k-1)) := Nat.le_mul_of_pos_left _ (by omega)
  rw [ExecuteDecomp.bit_succ_operations,ExecuteDecomp.native_succ_operations]
  nlinarith

/-- One common factor is preserved through every recursive child. The
only premise concerns public index lengths; coefficient lengths are already
charged by the native counter, with no all-register-width assumption here. -/
theorem execute_cost_refinement (k s W C : ℕ) (hk : 2≤k) (hC : 100*(W+2)≤C)
    (hindices : ∀ d ≤ s, (2*k^d).size≤W) (rom : ROM k) (a b : Array Signed) :
    (execute k rom s a b).operations ≤
      C*(ToomBitCost.execute ToomBitCost.bitPrimitives k s (arrayView a) (arrayView b)).operations := by
  induction s generalizing a b with
  | zero =>
    apply execute_zero_cost_refinement k W C rom a b
    · simpa only [pow_zero,mul_one] using hindices 0 le_rfl
    · exact hC
  | succ s ih =>
    apply execute_step_cost_refinement k s W C hk hC
    · exact (Nat.size_le_size (Nat.le_mul_of_pos_left _ (by decide : 0<2))).trans (hindices s (by omega))
    · exact hindices s (by omega)
    · simpa only [pow_succ',Nat.mul_assoc] using hindices (s+1) le_rfl
    · intro a b
      exact ih (fun d hd=>hindices d (by omega)) a b

/-- The actual signed-bit execution counter inherits the proved global
register budgets of the integer view. Every public index bound is derived
from the root dimensions, rather than supplied as a runtime assumption. -/
theorem execute_bit_cost (k s A : ℕ) (hk : 2≤k) (rom : ROM k) (a b : Array Signed)
    (ha : a.size=k^s) (hb : b.size=k^s)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView a)) (A:ℤ))
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView b)) (A:ℤ)) :
    (execute k rom s a b).operations ≤
      100*(ToomExecutionBound.bitBudget k s A+2)*
        ToomExecutionBound.bitMajorant k (ToomExecutionBound.localFactor k) s A := by
  let W := ToomExecutionBound.bitBudget k s A
  have hindices : ∀ d ≤ s, (2*k^d).size≤W := by
    intro d hd
    apply ToomExecutionBound.index_size_le_budget
    have hp := Nat.pow_le_pow_right (show 1≤k by omega) hd
    nlinarith
  have h := execute_cost_refinement k s W (100*(W+2)) hk le_rfl hindices rom a b
  have hn := ToomExecutionBound.execute_cost_bound k s A hk (arrayView a) (arrayView b)
    (by simpa only [arrayView,Array.size_map] using ha)
    (by simpa only [arrayView,Array.size_map] using hb) hfa hfb
  exact h.trans (Nat.mul_le_mul_left _ hn)

/-- For the fixed arity, the actual signed-bit recursive execution has
the certified near-linear coefficient-length exponent. Inputs are the
already materialized padded arrays; their formation and cyclic folding are
separate clients of this execution theorem. The fixed ROM is supplied data. -/
theorem padded_execute_fixed_bit_cost (q A : ℕ) (hq : 0<q)
    (rom : ROM (2^100000000)) (a b : Array Signed)
    (ha : a.size=(2^100000000)^(Nat.log (2^100000000) q+1))
    (hb : b.size=(2^100000000)^(Nat.log (2^100000000) q+1))
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView a)) (A:ℤ))
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView b)) (A:ℤ)) :
    ((execute (2^100000000) rom (Nat.log (2^100000000) q+1) a b).operations:ℝ) ≤
      ((100*(ToomExecutionBound.bitSlope (2^100000000)+14):ℕ):ℝ)*
      ((3*ToomExecutionBound.localFactor (2^100000000):ℕ):ℝ)*
      ((2:ℝ)^100000000)^(1.00000001:ℝ)*
      ((ToomExecutionBound.bitSlope (2^100000000)+13:ℕ):ℝ)^3*
      (q:ℝ)^(1.00000001:ℝ)*((q.size+A.size+2:ℕ):ℝ)^4 := by
  let k : ℕ := 2^100000000
  let s := Nat.log k q+1
  let W := ToomExecutionBound.bitBudget k s A
  let S := q.size+A.size+2
  let D := 100*(ToomExecutionBound.bitSlope k+14)
  have hk : 2≤k := two_le_two_pow 100000000 (by norm_num)
  have hS : 1≤S := by dsimp [S];omega
  have hW := ToomExecutionBound.padded_bitBudget_bound k q A hk hq
  have hf : 100*(W+2)≤D*S := by dsimp [W,s,D,S];nlinarith
  have hfR : ((100*(W+2):ℕ):ℝ)≤(D:ℝ)*(S:ℝ) := by exact_mod_cast hf
  have h := execute_bit_cost k s A hk rom a b ha hb hfa hfb
  have hR : ((execute k rom s a b).operations:ℝ) ≤
      ((100*(W+2):ℕ):ℝ)*
        (ToomExecutionBound.bitMajorant k (ToomExecutionBound.localFactor k) s A:ℝ) := by
    exact_mod_cast h
  have hM := ToomExecutionBound.fixed_bitMajorant_at_length
    (ToomExecutionBound.localFactor k) q A hq
  change _ ≤ (D:ℝ)*((3*ToomExecutionBound.localFactor k:ℕ):ℝ)*
      ((2:ℝ)^100000000)^(1.00000001:ℝ)*
      ((ToomExecutionBound.bitSlope k+13:ℕ):ℝ)^3*
      (q:ℝ)^(1.00000001:ℝ)*(S:ℝ)^4
  calc
    _ ≤ ((100*(W+2):ℕ):ℝ)*
        (ToomExecutionBound.bitMajorant k (ToomExecutionBound.localFactor k) s A:ℝ) := hR
    _ ≤ ((D:ℝ)*(S:ℝ))*
        (((3*ToomExecutionBound.localFactor k:ℕ):ℝ)*
          ((2:ℝ)^100000000)^(1.00000001:ℝ)*
          ((ToomExecutionBound.bitSlope k+13:ℕ):ℝ)^3*
          (q:ℝ)^(1.00000001:ℝ)*(S:ℝ)^3) := by
      apply mul_le_mul hfR
      · exact hM
      · exact Nat.cast_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg S)
    _ = _ := by ring

/-- Correct full output array and actual execution counter are properties
of the same signed-bit run. -/
theorem execute_correct_and_bit_cost (k s A : ℕ) (hk : 2≤k) (rom : ROM k) (a b : Array Signed)
    (ha : a.size=k^s) (hb : b.size=k^s)
    (hfa : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView a)) (A:ℤ))
    (hfb : ToomCook.CoeffBound (ToomBitCost.arrayPolynomial (arrayView b)) (A:ℤ)) :
    arrayView (execute k rom s a b).value =
      Array.ofFn (fun j : Fin (2*k^s)=>
        (ToomBitCost.arrayPolynomial (arrayView a)*ToomBitCost.arrayPolynomial (arrayView b)).coeff j.val) ∧
    (execute k rom s a b).operations ≤ 100*(ToomExecutionBound.bitBudget k s A+2)*
      ToomExecutionBound.bitMajorant k (ToomExecutionBound.localFactor k) s A :=
  ⟨execute_product k rom s hk a b ha hb,execute_bit_cost k s A hk rom a b ha hb hfa hfb⟩

#print axioms padded_execute_fixed_bit_cost
#print axioms execute_correct_and_bit_cost
#print axioms execute_cost_refinement
#print axioms execute_bit_cost
#print axioms execute_step_cost_refinement
#print axioms evaluate_cost_refinement
#print axioms interpolate_cost_refinement
#print axioms recombine_cost_refinement
#print axioms tabulateInteger_cost_refinement
end ThinMatrix.BitArraySimulation
