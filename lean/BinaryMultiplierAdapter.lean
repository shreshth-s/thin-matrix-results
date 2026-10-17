import BinaryArrayFFT
import ThinMatrixBackend

/-!
An explicit boundary adapter for the binary FFT and the backend's stored
integer-vector interface. The original integer inputs are serialized by a
division-by-two loop, the bound guard runs on their stored Boolean digits,
and the output is decoded by a charged bit traversal. The FFT itself keeps
all intermediate coefficients in binary registers.

The adapter captures a positive magnitude bound. Its fallback makes the
value interface total; the fast counter theorem proves that bounded actual
operands always use the binary branch. No cost bound for the fallback is
asserted. Boundary counters price the bit length of each shift, append and
copy; they are not a theorem about the Lean evaluator or a word-machine
compiler.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ThinMatrix.BinaryMultiplierAdapter
open scoped BigOperators
open IntegerArithmetic FFTBitCost
open ThinMatrixBackend

/-- The nonzero natural-number encoding equation, with no padding bits. -/
theorem bits_nonzero (n : ℕ) (hn : n≠0) : n.bits=n.bodd::n.div2.bits := by
  have hc : n.div2=0 → n.bodd=true := by
    intro hd
    have he := Nat.bit_bodd_div2 n
    rw [hd] at he
    cases hb : n.bodd <;> simp_all [Nat.bit]
  simpa only [Nat.bit_bodd_div2] using (Nat.bits_append_bit n.div2 n.bodd hc)

theorem div2_size (n : ℕ) (hn : n≠0) : n.div2.size+1=n.size := by
  have h := congrArg List.length (bits_nonzero n hn)
  simpa only [Nat.size_eq_bits_len,List.length_cons] using h.symm

/-- Actual boundary serialization. Each branch extracts one stored bit and
shifts the current original-input magnitude. The charge includes traversing
that magnitude rather than assigning unit cost to an unbounded shift. -/
def encodeNat (n : ℕ) : BinaryResult (List Bool) :=
  if hn : n=0 then ⟨[],1⟩ else
    let tail := encodeNat n.div2
    ⟨n.bodd::tail.value,tail.bitSteps+8*(n.size+1)⟩
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem encodeNat_value (n : ℕ) : (encodeNat n).value=n.bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [encodeNat]
    split_ifs with hn
    · simp [hn]
    · dsimp only
      rw [ih n.div2 (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),bits_nonzero n hn]

theorem encodeNat_cost (n : ℕ) : (encodeNat n).bitSteps ≤ 8*(n.size+1)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [encodeNat]
    split_ifs with hn
    · subst n; norm_num
    · have ht := ih n.div2 (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      have hs := div2_size n hn
      dsimp only
      nlinarith

def encodeInteger (z : ℤ) : BinaryResult BinaryArrayFFT.Integer :=
  let magnitude := encodeNat z.natAbs
  let bits : SignedBits := ⟨decide (z<0),magnitude.value⟩
  ⟨⟨bits,by
    dsimp [bits]
    rw [encodeNat_value]
    change (ofInt z).magnitude.length=(signedValue (ofInt z)).natAbs.size
    rw [ofInt_correct]
    exact ofInt_length z⟩,magnitude.bitSteps+2⟩

theorem encodeInteger_view (z : ℤ) : (encodeInteger z).value.view=z := by
  simp only [encodeInteger,BinaryArrayFFT.Integer.view,encodeNat_value]
  exact ofInt_correct z

theorem encodeInteger_cost (z : ℤ) :
    (encodeInteger z).bitSteps ≤ 10*(z.natAbs.size+1)^2 := by
  have h := encodeNat_cost z.natAbs
  change (encodeNat z.natAbs).bitSteps+2≤_
  nlinarith [Nat.one_le_pow 2 (z.natAbs.size+1) (by omega)]

/-- Boundary deserialization. Each growing accumulator shift/add is
charged by its current bit length; the coefficient arithmetic inside the
FFT never uses this native representation. -/
def decodeNat : List Bool → BinaryResult ℕ
  | [] => ⟨0,1⟩
  | b::bs =>
    let tail := decodeNat bs
    ⟨digit b+2*tail.value,tail.bitSteps+8*(bs.length+1)⟩

theorem decodeNat_value (bs : List Bool) : (decodeNat bs).value=value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [decodeNat,value,ih]

theorem decodeNat_cost (bs : List Bool) :
    (decodeNat bs).bitSteps ≤ 8*(bs.length+1)^2 := by
  induction bs with
  | nil => norm_num [decodeNat]
  | cons b bs ih => simp only [decodeNat,List.length_cons];nlinarith

def decodeInteger (z : BinaryArrayFFT.Integer) : BinaryResult ℤ :=
  let magnitude := decodeNat z.bits.magnitude
  ⟨if z.bits.negative then -(magnitude.value:ℤ) else (magnitude.value:ℤ),
    magnitude.bitSteps+2*(z.bits.magnitude.length+1)⟩

theorem decodeInteger_value (z : BinaryArrayFFT.Integer) : (decodeInteger z).value=z.view := by
  simp only [decodeInteger,decodeNat_value,BinaryArrayFFT.Integer.view,signedValue]

theorem decodeInteger_cost (z : BinaryArrayFFT.Integer) :
    (decodeInteger z).bitSteps ≤ 10*(z.view.natAbs.size+1)^2 := by
  have h := decodeNat_cost z.bits.magnitude
  change (decodeNat z.bits.magnitude).bitSteps+2*(z.bits.magnitude.length+1)≤_
  rw [z.canonical] at h ⊢
  change _≤10*((signedValue z.bits).natAbs.size+1)^2
  nlinarith

def encodeVector {q : ℕ} (a : Vector ℤ q) : BinaryResult (Vector BinaryArrayFFT.Integer q) :=
  let cells := BinaryArrayFFT.tabulate q (fun i =>
    let encoded := encodeInteger (a.get i)
    ⟨encoded.value,encoded.bitSteps+i.val.size+2⟩)
  ⟨⟨cells.value,by rw [BinaryArrayFFT.tabulate_value];simp⟩,cells.bitSteps+4*q⟩

theorem encodeVector_get {q : ℕ} (a : Vector ℤ q) (i : Fin q) :
    ((encodeVector a).value.get i).view=a.get i := by
  simp only [encodeVector,Vector.get,BinaryArrayFFT.tabulate_value,Array.getElem_ofFn]
  exact encodeInteger_view _

theorem encodeVector_getD {q : ℕ} (a : Vector ℤ q) (i : Fin q) :
    ((encodeVector a).value.toArray.getD i.val BinaryArrayFFT.zeroInteger).view=a.get i := by
  simpa only [Array.getD,Vector.size_toArray,i.isLt,dif_pos,Vector.get,Array.getInternal_eq_getElem,Fin.val_cast] using
    encodeVector_get a i

theorem encodeVector_cost {q : ℕ} (a : Vector ℤ q) (A : ℕ)
    (ha : ∀ i, (a.get i).natAbs≤A) :
    (encodeVector a).bitSteps ≤ q*(10*(A.size+1)^2+q.size+6) := by
  have hcell (i : Fin q) :
      (encodeInteger (a.get i)).bitSteps+i.val.size+2 ≤ 10*(A.size+1)^2+q.size+2 := by
    have he := encodeInteger_cost (a.get i)
    have hw := Nat.size_le_size (ha i)
    have hi := Nat.size_le_size i.isLt.le
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2
    nlinarith
  have ht := BinaryArrayFFT.tabulate_bitSteps_bound q
    (fun i : Fin q =>
      (⟨(encodeInteger (a.get i)).value,(encodeInteger (a.get i)).bitSteps+i.val.size+2⟩ :
        BinaryResult BinaryArrayFFT.Integer))
    (10*(A.size+1)^2+q.size+2) hcell
  change _+4*q≤_
  nlinarith

/-- Compare actual stored magnitudes by the subtractor's final borrow bit. -/
def checkInteger (bound : List Bool) (z : BinaryArrayFFT.Integer) : BinaryResult Bool :=
  let comparison := subCounted bound z.bits.magnitude false
  ⟨!comparison.1.2,comparison.2+2⟩

theorem checkInteger_true (bound : List Bool) (z : BinaryArrayFFT.Integer) :
    (checkInteger bound z).value=true ↔ z.view.natAbs≤value bound := by
  have hb := subBits_borrow bound z.bits.magnitude
  rw [←signedValue_natAbs z.bits] at hb
  simp only [checkInteger,(subCounted_projections _ _ _).1]
  have hn (b : Bool) : (!b)=true ↔ b≠true := by cases b <;> decide
  rw [hn]
  change (¬ (subBits bound z.bits.magnitude false).2=true) ↔ _
  rw [hb]
  exact Nat.not_lt

theorem checkInteger_cost (bound : List Bool) (z : BinaryArrayFFT.Integer) :
    (checkInteger bound z).bitSteps = 12*max bound.length z.view.natAbs.size+3 := by
  simp only [checkInteger,(subCounted_projections _ _ _).2,columnSteps_eq,z.canonical,
    BinaryArrayFFT.Integer.view]

def checkVector {q : ℕ} (bound : List Bool) (a : Vector BinaryArrayFFT.Integer q) :
    BinaryResult Bool :=
  let cells := BinaryArrayFFT.tabulate q (fun i =>
    let checked := checkInteger bound (a.get i)
    ⟨checked.value,checked.bitSteps+i.val.size+2⟩)
  ⟨cells.value.toList.all id,cells.bitSteps+4*q⟩

theorem checkVector_true {q : ℕ} (bound : List Bool) (a : Vector BinaryArrayFFT.Integer q) :
    (checkVector bound a).value=true ↔ ∀i, (a.get i).view.natAbs≤value bound := by
  simp only [checkVector,BinaryArrayFFT.tabulate_value,Array.toList_ofFn,List.all_eq_true]
  constructor
  · intro h i
    exact (checkInteger_true bound (a.get i)).mp
      (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro h x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (checkInteger_true bound (a.get i)).mpr (h i)

theorem checkVector_cost {q : ℕ} (A : ℕ) (a : Vector BinaryArrayFFT.Integer q)
    (ha : ∀i, (a.get i).view.natAbs≤A) :
    (checkVector (encodeNat A).value a).bitSteps ≤ q*(12*A.size+q.size+9) := by
  have hcell (i : Fin q) :
      (checkInteger (encodeNat A).value (a.get i)).bitSteps+i.val.size+2 ≤
        12*A.size+q.size+5 := by
    rw [checkInteger_cost,encodeNat_value,Nat.size_eq_bits_len]
    have hw := Nat.size_le_size (ha i)
    rw [max_eq_left hw]
    have hi := Nat.size_le_size i.isLt.le
    omega
  have ht := BinaryArrayFFT.tabulate_bitSteps_bound q
    (fun i : Fin q =>
      (⟨(checkInteger (encodeNat A).value (a.get i)).value,
        (checkInteger (encodeNat A).value (a.get i)).bitSteps+i.val.size+2⟩ : BinaryResult Bool))
    (12*A.size+q.size+5) hcell
  change _+4*q≤_
  nlinarith

def decodeVector (q : ℕ) (a : Array BinaryArrayFFT.Integer) : BinaryResult (Vector ℤ q) :=
  let cells := BinaryArrayFFT.tabulate q (fun i =>
    let decoded := decodeInteger (a.getD i.val BinaryArrayFFT.zeroInteger)
    ⟨decoded.value,decoded.bitSteps+i.val.size+2⟩)
  ⟨⟨cells.value,by rw [BinaryArrayFFT.tabulate_value];simp⟩,cells.bitSteps+4*q⟩

theorem decodeVector_get (q : ℕ) (a : Array BinaryArrayFFT.Integer) (i : Fin q) :
    (decodeVector q a).value.get i=(a.getD i.val BinaryArrayFFT.zeroInteger).view := by
  simp only [decodeVector,Vector.get,BinaryArrayFFT.tabulate_value,Array.getElem_ofFn]
  exact decodeInteger_value _

theorem decodeVector_cost (q W : ℕ) (a : Array BinaryArrayFFT.Integer)
    (ha : ∀i : Fin q, (a.getD i.val BinaryArrayFFT.zeroInteger).view.natAbs.size≤W) :
    (decodeVector q a).bitSteps ≤ q*(10*(W+1)^2+q.size+6) := by
  have hcell (i : Fin q) :
      (decodeInteger (a.getD i.val BinaryArrayFFT.zeroInteger)).bitSteps+i.val.size+2 ≤
        10*(W+1)^2+q.size+2 := by
    have hd := decodeInteger_cost (a.getD i.val BinaryArrayFFT.zeroInteger)
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right (ha i) 1) 2
    have hi := Nat.size_le_size i.isLt.le
    nlinarith
  have ht := BinaryArrayFFT.tabulate_bitSteps_bound q
    (fun i : Fin q =>
      (⟨(decodeInteger (a.getD i.val BinaryArrayFFT.zeroInteger)).value,
        (decodeInteger (a.getD i.val BinaryArrayFFT.zeroInteger)).bitSteps+i.val.size+2⟩ :
          BinaryResult ℤ)) (10*(W+1)^2+q.size+2) hcell
  change _+4*q≤_
  nlinarith

structure Prepared (q : ℕ) where
  left : Vector BinaryArrayFFT.Integer q
  right : Vector BinaryArrayFFT.Integer q
  valid : Bool
  bitSteps : ℕ

def prepare {q : ℕ} (A : ℕ) (a b : Vector ℤ q) : Prepared q :=
  let bound := encodeNat A
  let left := encodeVector a
  let right := encodeVector b
  let leftCheck := checkVector bound.value left.value
  let rightCheck := checkVector bound.value right.value
  ⟨left.value,right.value,leftCheck.value && rightCheck.value,
    bound.bitSteps+left.bitSteps+right.bitSteps+leftCheck.bitSteps+rightCheck.bitSteps+4⟩

theorem prepare_left {q : ℕ} (A : ℕ) (a b : Vector ℤ q) (i : Fin q) :
    ((prepare A a b).left.toArray.getD i.val BinaryArrayFFT.zeroInteger).view=a.get i :=
  encodeVector_getD a i

theorem prepare_right {q : ℕ} (A : ℕ) (a b : Vector ℤ q) (i : Fin q) :
    ((prepare A a b).right.toArray.getD i.val BinaryArrayFFT.zeroInteger).view=b.get i :=
  encodeVector_getD b i

theorem prepare_valid {q : ℕ} (A : ℕ) (a b : Vector ℤ q) :
    (prepare A a b).valid=true ↔
      (∀i, (a.get i).natAbs≤A) ∧ (∀i, (b.get i).natAbs≤A) := by
  simp only [prepare,Bool.and_eq_true,checkVector_true,encodeNat_value,value_bits,
    encodeVector_get]

def binaryRun (q A : ℕ) (inputs : Prepared q) : Vector ℤ q × ℕ :=
  let product := BinaryArrayFFT.multiplication q A inputs.left.toArray inputs.right.toArray
  let decoded := decodeVector q product.value
  (decoded.value,inputs.bitSteps+product.bitSteps+product.arrayActions+decoded.bitSteps)

/-- The guard is evaluated on actual Boolean magnitudes. The fallback is
used only when a caller violates the captured bound; every fast-bound
application below proves that this branch cannot be taken. -/
def run {q : ℕ} (A : ℕ) (a b : Vector ℤ q) : Vector ℤ q × ℕ :=
  let inputs := prepare A a b
  if inputs.valid then binaryRun q A inputs else
    let fallback := cyclicVectorProduct a b
    (fallback.1,inputs.bitSteps+fallback.2)

theorem prepared_asCyclic_left {q : ℕ} (A : ℕ) (a b : Vector ℤ q) :
    ArrayFFT.asCyclic q (BinaryArrayFFT.viewIntegers (prepare A a b).left.toArray)=a.get := by
  funext i
  simp only [ArrayFFT.asCyclic,BinaryArrayFFT.viewIntegers_getD,prepare_left]

theorem prepared_asCyclic_right {q : ℕ} (A : ℕ) (a b : Vector ℤ q) :
    ArrayFFT.asCyclic q (BinaryArrayFFT.viewIntegers (prepare A a b).right.toArray)=b.get := by
  funext i
  simp only [ArrayFFT.asCyclic,BinaryArrayFFT.viewIntegers_getD,prepare_right]

theorem run_correct {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (r : Fin q) :
    (run A a b).1.get r=CyclicRing.convolution a.get b.get r := by
  unfold run
  dsimp only
  split_ifs with hg
  · have hbounds := (prepare_valid A a b).mp hg
    simp only [binaryRun,decodeVector_get]
    rw [BinaryArrayFFT.multiplication_correct q A hA _ _
      (fun i => by rw [prepare_left]; exact hbounds.1 i)
      (fun i => by rw [prepare_right]; exact hbounds.2 i)]
    rw [prepared_asCyclic_left,prepared_asCyclic_right]
  · exact cyclicVectorProduct_correct a b r

def boundedBinaryFullMultiplier (q A : ℕ) [NeZero q] (hA : 1≤A) : FullMultiplier q :=
  ⟨run A,run_correct A hA⟩

theorem run_of_bounds {q : ℕ} (A : ℕ) (a b : Vector ℤ q)
    (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    run A a b=binaryRun q A (prepare A a b) := by
  have hg := (prepare_valid A a b).mpr ⟨ha,hb⟩
  simp only [run,hg,if_true]

theorem convolution_magnitude {q : ℕ} [NeZero q] (A : ℕ) (a b : Vector ℤ q)
    (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) (r : Fin q) :
    (CyclicRing.convolution a.get b.get r).natAbs≤q*A^2 := by
  unfold CyclicRing.convolution
  apply (Int.natAbs_sum_le _ _).trans
  calc
    ∑i : Fin q, (a.get i*b.get (r-i)).natAbs ≤ ∑_i : Fin q, A^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul,pow_two]
      exact Nat.mul_le_mul (ha i) (hb (r-i))
    _ = _ := by simp

theorem size_mul (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  calc
    a*b≤2^a.size*b := Nat.mul_le_mul_right b (Nat.lt_size_self a).le
    _<2^a.size*2^b.size := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)
    _=2^(a.size+b.size) := (pow_add _ _ _).symm

theorem product_output_bits {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A)
    (r : Fin q) :
    ((BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).value.getD r.val BinaryArrayFFT.zeroInteger).view.natAbs.size≤
        q.size+2*A.size := by
  rw [BinaryArrayFFT.multiplication_correct q A hA _ _
    (fun i => by rw [prepare_left];exact ha i)
    (fun i => by rw [prepare_right];exact hb i),prepared_asCyclic_left,prepared_asCyclic_right]
  have hm := Nat.size_le_size (convolution_magnitude A a b ha hb r)
  have h1 := size_mul q (A*A)
  have h2 := size_mul A A
  rw [pow_two] at hm
  omega

def width (q A : ℕ) : ℕ := q.size+A.size+102

def workBound (q A : ℕ) : ℕ := 1180591620717411303424*q*(width q A)^11

theorem log2_le_size (n : ℕ) : n.log2≤n.size := by
  by_cases hn : n=0
  · simp [hn]
  · exact ((Nat.log2_lt hn).mpr (Nat.lt_size_self n)).le

theorem prepare_cost {q : ℕ} [NeZero q] (A : ℕ) (a b : Vector ℤ q)
    (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    (prepare A a b).bitSteps ≤ 100*q*(width q A)^2 := by
  have hq := NeZero.pos q
  have hl := encodeVector_cost a A ha
  have hr := encodeVector_cost b A hb
  have hcl := checkVector_cost A (encodeVector a).value (fun i => by
    rw [encodeVector_get];exact ha i)
  have hcr := checkVector_cost A (encodeVector b).value (fun i => by
    rw [encodeVector_get];exact hb i)
  have he := encodeNat_cost A
  have henc : 10*(A.size+1)^2+q.size+6≤20*(width q A)^2 := by
    dsimp [width]
    nlinarith
  have hguard : 12*A.size+q.size+9≤20*(width q A)^2 := by
    dsimp [width]
    nlinarith
  have hbound : 8*(A.size+1)^2+4≤20*q*(width q A)^2 := by
    have hs : 8*(A.size+1)^2+4≤20*(width q A)^2 := by dsimp [width];nlinarith
    have hmul := Nat.mul_le_mul_right (20*(width q A)^2) (show 1≤q by omega)
    nlinarith
  have hl' := hl.trans (Nat.mul_le_mul_left q henc)
  have hr' := hr.trans (Nat.mul_le_mul_left q henc)
  have hcl' := hcl.trans (Nat.mul_le_mul_left q hguard)
  have hcr' := hcr.trans (Nat.mul_le_mul_left q hguard)
  change (encodeNat A).bitSteps+(encodeVector a).bitSteps+(encodeVector b).bitSteps+
    (checkVector (encodeNat A).value (encodeVector a).value).bitSteps+
    (checkVector (encodeNat A).value (encodeVector b).value).bitSteps+4≤_
  nlinarith

theorem binaryCore_cost {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).bitSteps+
    (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).arrayActions ≤
        147573952589676412928*q*(width q A)^11 := by
  have h := BinaryArrayFFT.multiplication_totalSteps_bound q A
    (prepare A a b).left.toArray (prepare A a b).right.toArray hA
    (fun i => by rw [prepare_left];exact ha i)
    (fun i => by rw [prepare_right];exact hb i)
  have hq : q.log2+3≤width q A := by have := log2_le_size q;dsimp [width];omega
  have hw : q.log2+A.log2+102≤width q A := by
    have := log2_le_size q
    have := log2_le_size A
    dsimp [width]
    omega
  calc
    _≤147573952589676412928*(q.log2+3)*q*(q.log2+A.log2+102)^10 := h
    _≤147573952589676412928*(width q A)*q*(width q A)^10 := by gcongr
    _=147573952589676412928*q*(width q A)^11 := by ring

theorem decodeProduct_cost {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    (decodeVector q (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).value).bitSteps≤100*q*(width q A)^2 := by
  have h := decodeVector_cost q (q.size+2*A.size)
    (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).value
    (product_output_bits A hA a b ha hb)
  have hpoint : 10*(q.size+2*A.size+1)^2+q.size+6≤100*(width q A)^2 := by
    have hw : q.size+2*A.size+1≤2*width q A := by dsimp [width];omega
    have hp := Nat.pow_le_pow_left hw 2
    have hs : 1≤width q A := by dsimp [width];omega
    have hl : q.size+6≤width q A := by dsimp [width];omega
    have hlin : q.size+6≤(width q A)^2 := by nlinarith
    simp only [mul_pow] at hp
    norm_num only [Nat.reducePow] at hp
    nlinarith
  exact h.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    Nat.mul_le_mul_left q hpoint)

/-- The returned counter contains the input encoders, actual bit guard,
binary FFT bit and array actions, and all q decoded output cells. -/
theorem bounded_run_work {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    ((boundedBinaryFullMultiplier q A hA).run a b).2≤workBound q A := by
  change (run A a b).2≤_
  rw [run_of_bounds A a b ha hb]
  have hp := prepare_cost A a b ha hb
  have hc := binaryCore_cost A hA a b ha hb
  have hd := decodeProduct_cost A hA a b ha hb
  have hs : 1≤width q A := by dsimp [width];omega
  have hpow : (width q A)^2≤(width q A)^11 := Nat.pow_le_pow_right hs (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left (100*q) hpow)
  have hd' := hd.trans (Nat.mul_le_mul_left (100*q) hpow)
  change (prepare A a b).bitSteps+
    (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).bitSteps+
    (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).arrayActions+
    (decodeVector q (BinaryArrayFFT.multiplication q A (prepare A a b).left.toArray
      (prepare A a b).right.toArray).value).bitSteps≤_
  dsimp only [workBound]
  nlinarith

theorem bounded_correct_and_work {q : ℕ} [NeZero q] (A : ℕ) (hA : 1≤A)
    (a b : Vector ℤ q) (ha : ∀i, (a.get i).natAbs≤A) (hb : ∀i, (b.get i).natAbs≤A) :
    (∀r, ((boundedBinaryFullMultiplier q A hA).run a b).1.get r=
      CyclicRing.convolution a.get b.get r) ∧
    ((boundedBinaryFullMultiplier q A hA).run a b).2≤workBound q A :=
  ⟨run_correct A hA a b,bounded_run_work A hA a b ha hb⟩

end ThinMatrix.BinaryMultiplierAdapter

#print axioms ThinMatrix.BinaryMultiplierAdapter.encodeNat_value
#print axioms ThinMatrix.BinaryMultiplierAdapter.encodeNat_cost
#print axioms ThinMatrix.BinaryMultiplierAdapter.encodeInteger_view
#print axioms ThinMatrix.BinaryMultiplierAdapter.decodeInteger_value
#print axioms ThinMatrix.BinaryMultiplierAdapter.checkVector_true
#print axioms ThinMatrix.BinaryMultiplierAdapter.prepare_valid
#print axioms ThinMatrix.BinaryMultiplierAdapter.run_correct
#print axioms ThinMatrix.BinaryMultiplierAdapter.bounded_run_work
#print axioms ThinMatrix.BinaryMultiplierAdapter.bounded_correct_and_work
