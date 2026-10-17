import ToomBitCost

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-!
# Persistent signed-bit arrays for the Toom coefficient execution

The runtime values in this module are Boolean lists and arrays of those
lists. Integer denotations and `ofInt` occur in representation proofs only;
they are not called by the executable arithmetic or array programs.
Read-only constants are supplied as already stored signed-bit data.

Array indices/control values are bounded natural machine addresses. Their
copies, address lengths and bit-to-address decoding are explicitly charged.
Realizing this bit-serial instruction model in the project's word machine
is a separate compilation theorem.
-/

namespace ThinMatrix.BitArraySimulation

open scoped BigOperators
open ToomCook
open ToomBitCost.Counted

def Canonical (x : IntegerArithmetic.SignedBits) : Prop := x = IntegerArithmetic.ofInt (IntegerArithmetic.signedValue x)
abbrev Signed := {x : IntegerArithmetic.SignedBits // Canonical x}

def denote (x : Signed) : ℤ := IntegerArithmetic.signedValue x.val

def zero : Signed := ⟨⟨false,[]⟩,rfl⟩
def one : Signed := ⟨⟨false,[true]⟩,rfl⟩

@[simp] theorem denote_zero : denote zero = 0 := rfl
@[simp] theorem denote_one : denote one = 1 := rfl

theorem canonical_eq (x : Signed) : x.val = IntegerArithmetic.ofInt (denote x) := x.property

theorem magnitude_length (x : Signed) : x.val.magnitude.length = (denote x).natAbs.size := by
  rw [canonical_eq, IntegerArithmetic.ofInt_length]

theorem normalized_canonical (raw : IntegerArithmetic.SignedBits × ℕ) :
    Canonical (IntegerArithmetic.normalizeResult raw).1 := by
  unfold Canonical
  rw [IntegerArithmetic.normalizeResult_value, IntegerArithmetic.ofInt_correct]

def copyBits : List Bool → Counted (List Bool)
  | [] => ⟨[],1⟩
  | b::bs =>
    let tail := copyBits bs
    ⟨b::tail.value,tail.operations+2⟩

theorem copyBits_value (bs : List Bool) : (copyBits bs).value = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [copyBits,ih]

theorem copyBits_cost (bs : List Bool) : (copyBits bs).operations = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [copyBits,ih]; omega

def copy (x : Signed) : Counted Signed :=
  let bits := copyBits x.val.magnitude
  ⟨⟨⟨x.val.negative,bits.value⟩,by
      rw [copyBits_value]
      exact x.property⟩,bits.operations+1⟩

theorem copy_value (x : Signed) : (copy x).value = x := by
  apply Subtype.ext
  simp only [copy,copyBits_value]

theorem copy_cost (x : Signed) : (copy x).operations = 2*(denote x).natAbs.size+2 := by
  simp only [copy,copyBits_cost,magnitude_length]

def add (x y : Signed) : Counted Signed :=
  let result := IntegerArithmetic.normalizedAddCounted x.val y.val
  ⟨⟨result.1,normalized_canonical (IntegerArithmetic.signedAddCounted x.val y.val)⟩,result.2⟩

def mul (x y : Signed) : Counted Signed :=
  let result := IntegerArithmetic.normalizedMulCounted x.val y.val
  ⟨⟨result.1,normalized_canonical (IntegerArithmetic.signedMulCounted x.val y.val)⟩,result.2⟩

/-- The divisor is copied from a fixed read-only table. -/
def divide (divisor : List Bool) (x : Signed) : Counted Signed :=
  let stored := copyBits divisor
  let result := IntegerArithmetic.normalizedDivideCounted stored.value x.val
  ⟨⟨result.1,normalized_canonical (IntegerArithmetic.signedDivideCounted stored.value x.val)⟩,
    result.2+stored.operations+1⟩

theorem add_value (x y : Signed) : denote (add x y).value = denote x+denote y := by
  simp only [add,denote,IntegerArithmetic.normalizedAddCounted_value,IntegerArithmetic.ofInt_correct]

theorem mul_value (x y : Signed) : denote (mul x y).value = denote x*denote y := by
  simp only [mul,denote,IntegerArithmetic.normalizedMulCounted_value,IntegerArithmetic.ofInt_correct]

theorem add_cost (x y : Signed) :
    (add x y).operations = (ToomBitCost.bitPrimitives.add (denote x) (denote y)).operations := by
  simp only [add,ToomBitCost.bitPrimitives]
  rw [canonical_eq x,canonical_eq y]

theorem mul_cost (x y : Signed) :
    (mul x y).operations = (ToomBitCost.bitPrimitives.mul (denote x) (denote y)).operations := by
  simp only [mul,ToomBitCost.bitPrimitives]
  rw [canonical_eq x,canonical_eq y]

theorem divide_value (D : ℕ) (x : Signed) (divisor : List Bool) (hD : divisor=D.bits) :
    denote (divide divisor x).value = (ToomBitCost.bitPrimitives.divide D (denote x)).value := by
  subst divisor
  simp only [divide,copyBits_value,denote,ToomBitCost.bitPrimitives]
  rw [canonical_eq x]
  simp only [IntegerArithmetic.ofInt_correct]

theorem divide_cost (D : ℕ) (x : Signed) (divisor : List Bool) (hD : divisor=D.bits) :
    (divide divisor x).operations ≤ 2*(ToomBitCost.bitPrimitives.divide D (denote x)).operations := by
  subst divisor
  simp only [divide,copyBits_value,copyBits_cost,ToomBitCost.bitPrimitives]
  rw [canonical_eq x,Nat.size_eq_bits_len]
  omega

/-- Only a sign bit changes. Zero is recognized by the empty canonical
magnitude, so negative zero is never persisted. -/
def negate (x : Signed) : Counted Signed :=
  if h : x.val.magnitude=[] then ⟨zero,4⟩
  else ⟨⟨IntegerArithmetic.signedNeg x.val,by
      have hm : IntegerArithmetic.normalize x.val.magnitude=x.val.magnitude := by
        rw [canonical_eq x]
        simp only [IntegerArithmetic.ofInt,IntegerArithmetic.normalize_eq_bits,IntegerArithmetic.value_bits]
      have hn := IntegerArithmetic.normalizeSigned_eq_ofInt (IntegerArithmetic.signedNeg x.val)
      simpa only [Canonical,IntegerArithmetic.normalizeSigned,IntegerArithmetic.signedNeg,hm,h,if_false] using hn⟩,4⟩

theorem negate_value (x : Signed) : denote (negate x).value = -denote x := by
  unfold negate
  split_ifs with h
  · simp only [denote_zero]
    unfold denote IntegerArithmetic.signedValue
    rw [h]
    simp [IntegerArithmetic.value]
  · exact IntegerArithmetic.signedNeg_correct x.val

theorem negate_cost (x : Signed) : (negate x).operations = 4 := by
  unfold negate
  split_ifs <;> rfl

/-- This decoder operates on the bits already stored in runtime data.
It uses bounded natural address addition, rather than an integer
interpretation or conversion of a coefficient. -/
def decodeAddress : List Bool → Counted ℕ
  | [] => ⟨0,1⟩
  | b::bs =>
    let tail := decodeAddress bs
    ⟨(if b then 1 else 0)+2*tail.value,tail.operations+5⟩

theorem decodeAddress_value (bs : List Bool) : (decodeAddress bs).value = IntegerArithmetic.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [decodeAddress,ih,IntegerArithmetic.value,IntegerArithmetic.digit]

theorem decodeAddress_cost (bs : List Bool) : (decodeAddress bs).operations = 5*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [decodeAddress,ih]; omega

theorem decodeMagnitude_value (x : Signed) :
    (decodeAddress x.val.magnitude).value = (denote x).natAbs := by
  rw [decodeAddress_value]
  exact (IntegerArithmetic.signedValue_natAbs x.val).symm

def arrayView (a : Array Signed) : Array ℤ := a.map denote
def childrenView (a : Array (Array Signed)) : Array (Array ℤ) := a.map arrayView

theorem arrayView_getD (a : Array Signed) (i : ℕ) :
    ((arrayView a)[i]?).getD 0 = denote ((a[i]?).getD zero) := by
  by_cases hi : i<a.size <;> simp [arrayView,hi]

theorem childrenView_getD (a : Array (Array Signed)) (i : ℕ) :
    ((childrenView a)[i]?).getD #[] = arrayView ((a[i]?).getD #[]) := by
  by_cases hi : i<a.size <;> simp [childrenView,hi,arrayView]

def readInteger (a : Array Signed) (i : ℕ) : Counted Signed :=
  let result := copy ((a[i]?).getD zero)
  ⟨result.value,result.operations+i.size+1⟩

theorem readInteger_value (a : Array Signed) (i : ℕ) :
    denote (readInteger a i).value = (ToomBitCost.readInteger (arrayView a) i).value := by
  simp only [readInteger,copy_value,ToomBitCost.readInteger,arrayView_getD]

theorem readInteger_cost (a : Array Signed) (i : ℕ) :
    (readInteger a i).operations ≤ 3*(ToomBitCost.readInteger (arrayView a) i).operations := by
  simp only [readInteger,copy_cost,ToomBitCost.readInteger,arrayView_getD]
  omega

def readChild (a : Array (Array Signed)) (r j : ℕ) : Counted Signed :=
  let child := (a[r]?).getD #[]
  let result := readInteger child j
  ⟨result.value,result.operations+r.size+1⟩

theorem readChild_value (a : Array (Array Signed)) (r j : ℕ) :
    denote (readChild a r j).value = (ToomBitCost.readChild (childrenView a) r j).value := by
  simp only [readChild,readInteger_value,ToomBitCost.readChild,ToomBitCost.readInteger,
    childrenView_getD,arrayView_getD]

theorem readChild_cost (a : Array (Array Signed)) (r j : ℕ) :
    (readChild a r j).operations ≤ 3*(ToomBitCost.readChild (childrenView a) r j).operations := by
  simp only [readChild,readInteger,copy_cost,ToomBitCost.readChild,
    childrenView_getD,arrayView_getD]
  omega

namespace IndexData
open IntegerArithmetic

def bitsZero : SignedBits := ⟨false,[]⟩
def bitsOne : SignedBits := ⟨false,[true]⟩

def copySigned (x : SignedBits) : SignedBits × ℕ :=
  let t := copyBits x.magnitude
  (⟨x.negative,t.value⟩,t.operations+1)

theorem copySigned_spec (x : SignedBits) : (copySigned x).1=x ∧
    (copySigned x).2=2*x.magnitude.length+2 := by
  cases x
  simp [copySigned,copyBits_value,copyBits_cost]

structure State where
  next : SignedBits
  rev : List SignedBits
  steps : ℕ

def loop : ℕ → State
  | 0 => ⟨bitsZero,[],1⟩
  | n+1 =>
    let prev := loop n
    let saved := copySigned prev.next
    let inc := normalizedAddCounted prev.next bitsOne
    ⟨inc.1,saved.1::prev.rev,prev.steps+saved.2+inc.2+(n+1).size+4⟩

theorem loop_spec (n : ℕ) : (loop n).next=ofInt (n:ℤ) ∧
    (loop n).rev=(List.range n).reverse.map (fun i : ℕ => ofInt (i:ℤ)) := by
  induction n with
  | zero => simp [loop,bitsZero,ofInt]
  | succ n ih =>
    simp only [loop,copySigned_spec,ih.1,ih.2,normalizedAddCounted_value,ofInt_correct]
    constructor
    · congr 1
    · simp [List.range_succ,List.reverse_append]

theorem increment_bound (n : ℕ) :
    (normalizedAddCounted (loop n).next bitsOne).2 ≤ 50*(n.size+2) := by
  have h := normalizedAddCounted_steps (loop n).next bitsOne
  have hl : (loop n).next.magnitude.length=n.size := by
    rw [(loop_spec n).1,ofInt_length]
    simp
  simp only [hl,bitsOne,List.length_cons,List.length_nil] at h
  exact h.trans (Nat.mul_le_mul_left 50 (by omega))

theorem loop_cost (n : ℕ) : (loop n).steps ≤ 60*n*(n.size+2)+1 := by
  induction n with
  | zero => simp [loop]
  | succ n ih =>
    have hi := increment_bound n
    have hc : (copySigned (loop n).next).2=2*n.size+2 := by
      rw [(copySigned_spec _).2,(loop_spec n).1,ofInt_length]
      simp
    have hs : n.size ≤ (n+1).size := Nat.size_le_size (by omega)
    have hm := Nat.mul_le_mul_left (60*n) (Nat.add_le_add_right hs 2)
    change (loop n).steps+(copySigned (loop n).next).2+
      (normalizedAddCounted (loop n).next bitsOne).2+(n+1).size+4 ≤ _
    rw [hc]
    nlinarith

def reverseLoop (n : ℕ) : List SignedBits → List SignedBits → List SignedBits × ℕ
  | [],acc => (acc,1)
  | x::xs,acc =>
    let r := reverseLoop n xs (x::acc)
    (r.1,r.2+3*(n.size+1))

theorem reverseLoop_spec (n : ℕ) (xs acc : List SignedBits) :
    (reverseLoop n xs acc).1=xs.reverse++acc ∧
    (reverseLoop n xs acc).2=3*xs.length*(n.size+1)+1 := by
  induction xs generalizing acc with
  | nil => simp [reverseLoop]
  | cons x xs ih =>
    constructor
    · simp only [reverseLoop,(ih _).1,List.reverse_cons,List.append_assoc,List.singleton_append]
    · simp only [reverseLoop,(ih _).2,List.length_cons]; ring

def arrayLoop (n : ℕ) : List SignedBits → Array SignedBits → Array SignedBits × ℕ
  | [],acc => (acc,1)
  | x::xs,acc =>
    let r := arrayLoop n xs (acc.push x)
    (r.1,r.2+3*(n.size+1))

theorem arrayLoop_spec (n : ℕ) (xs : List SignedBits) (acc : Array SignedBits) :
    (arrayLoop n xs acc).1=acc++xs.toArray ∧
    (arrayLoop n xs acc).2=3*xs.length*(n.size+1)+1 := by
  induction xs generalizing acc with
  | nil => simp [arrayLoop]
  | cons x xs ih =>
    constructor
    · simp only [arrayLoop,(ih _).1]
      calc
        acc.push x ++ xs.toArray = (acc++#[x])++xs.toArray := by
          exact congrArg (fun z => z++xs.toArray) Array.push_eq_append
        _ = acc++(#[x]++xs.toArray) := Array.append_assoc
        _ = acc++(x::xs).toArray := congrArg (fun z => acc++z) (List.toArray_cons x xs).symm
    · simp only [arrayLoop,(ih _).2,List.length_cons]; ring

def build (n : ℕ) : Array SignedBits × ℕ :=
  let b := loop n
  let r := reverseLoop n b.rev []
  let a := arrayLoop n r.1 #[]
  (a.1,b.steps+r.2+a.2+2)

theorem build_value (n : ℕ) :
    (build n).1=((List.range n).map (fun i : ℕ => ofInt (i:ℤ))).toArray := by
  simp only [build,reverseLoop_spec,arrayLoop_spec,(loop_spec n).2,
    List.append_nil,Array.empty_append,List.map_reverse,List.reverse_reverse]

theorem build_cost (n : ℕ) : (build n).2 ≤ 66*n*(n.size+2)+5 := by
  have hb := loop_cost n
  have hl : (loop n).rev.length=n := by simp [(loop_spec n).2]
  simp only [build,reverseLoop_spec,arrayLoop_spec]
  simp only [List.length_append,List.length_reverse,List.length_nil,add_zero,hl]
  nlinarith

theorem build_array (n : ℕ) :
    (build n).1=Array.ofFn (fun i : Fin n => ofInt (i.val:ℤ)) := by
  rw [build_value]
  apply Array.ext (by simp only [List.size_toArray,List.length_map,List.length_range,Array.size_ofFn])
  intro i hi hi'
  simp only [List.getElem_toArray,List.getElem_map,List.getElem_range,Array.getElem_ofFn]

theorem build_size (n : ℕ) : (build n).1.size=n := by rw [build_array]; simp

theorem build_get (n i : ℕ) (hi : i<(build n).1.size) : (build n).1[i]=ofInt (i:ℤ) := by
  simp only [build_array,Array.getElem_ofFn]

end IndexData

/-- The bit patterns generated by the increment loop are wrapped with
erased canonical-representation proofs and retained as an actual vector. -/
def indices (n : ℕ) : Counted (Vector Signed n) :=
  let raw := IndexData.build n
  ⟨Vector.ofFn (fun i =>
    ⟨raw.1[i.val]'(by rw [IndexData.build_size];exact i.isLt),by
      unfold Canonical
      rw [IndexData.build_get, IntegerArithmetic.ofInt_correct]⟩),
    raw.2+3*n*(n.size+1)⟩

theorem indices_value (n : ℕ) (i : Fin n) : denote ((indices n).value.get i) = (i.val:ℤ) := by
  simp only [indices,Vector.get_ofFn,denote,IndexData.build_get,IntegerArithmetic.ofInt_correct]

theorem indices_cost (n : ℕ) : (indices n).operations ≤ 70*n*(n.size+2)+5 := by
  have h := IndexData.build_cost n
  simp only [indices]
  nlinarith

def bind {α β : Type*} (x : Counted α) (f : α→ Counted β) : Counted β :=
  let y:=f x.value
  ⟨y.value,x.operations+y.operations⟩

def sequence {α β : Type*} (f : α→ Counted β) : List α→ Counted (List β)
  | [] => ⟨[],0⟩
  | x::xs =>
    let head:=f x
    let tail:=sequence f xs
    ⟨head.value::tail.value,head.operations+tail.operations⟩

theorem sequence_value {α β : Type*} (f : α→ Counted β) (xs : List α) :
    (sequence f xs).value=xs.map (fun x=>(f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sequence,ih,List.map_cons]

theorem sequence_operations {α β : Type*} (f : α→ Counted β) (xs : List α) :
    (sequence f xs).operations=(xs.map (fun x=>(f x).operations)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sequence,ih,List.map_cons,List.sum_cons]

def tabulate {α : Type*} (n : ℕ) (f : Fin n→ Counted α) : Counted (Array α) :=
  let cells:=sequence f (List.ofFn (id : Fin n→Fin n))
  ⟨cells.value.toArray,cells.operations+2*n⟩

theorem tabulate_value {α : Type*} (n : ℕ) (f : Fin n→ Counted α) :
    (tabulate n f).value=Array.ofFn (fun i=>(f i).value) := by
  simp [tabulate,sequence_value]

theorem tabulate_operations {α : Type*} (n : ℕ) (f : Fin n→ Counted α) :
    (tabulate n f).operations=(∑i,(f i).operations)+2*n := by
  simp only [tabulate,sequence_operations,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq]

/-- The runtime loop counter's binary patterns are generated once. Each
output coefficient is copied into its array slot after evaluation. -/
def tabulateInteger (n : ℕ) (f : Fin n→ Signed→ Counted Signed) : Counted (Array Signed) :=
  let indexTable:=indices n
  let output:=tabulate n (fun i=>
    bind (f i (indexTable.value.get i)) (fun x=>
      let stored:=copy x
      ⟨stored.value,stored.operations+i.val.size+2⟩))
  ⟨output.value,indexTable.operations+output.operations⟩

def readConstant (x : Signed) : Counted Signed :=
  let copied:=copy x
  ⟨copied.value,copied.operations+2⟩

theorem readConstant_value (x : Signed) : (readConstant x).value=x := by
  simp only [readConstant,copy_value]

theorem readConstant_cost (x : Signed) :
    (readConstant x).operations≤4*(ToomBitCost.readConstant (denote x)).operations := by
  simp only [readConstant,copy_cost,ToomBitCost.readConstant]
  omega

def dot {ι : Type*} (weight : ι→ Signed) (read : ι→ Counted Signed) : List ι→ Counted Signed
  | [] => ⟨zero,1⟩
  | i::is => bind (readConstant (weight i)) (fun w=>
      bind (read i) (fun x=>bind (mul w x) (fun product=>
        bind (dot weight read is) (fun tail=>add product tail))))

/-- Fixed-arity read-only data. All entries are already bit arrays before
the multiplication program starts; no integer-to-bits conversion is
performed by a runtime constant read. -/
structure ROM (k : ℕ) where
  base : Signed
  indexK : Vector Signed k
  indexM : Vector Signed (2*k-1)
  evaluation : Vector (Vector Signed k) (2*k-1)
  interpolation : Vector (Vector Signed (2*k-1)) (2*k-1)
  divisor : List Bool
  base_value : denote base=(k:ℤ)
  indexK_value : ∀i,denote (indexK.get i)=(i.val:ℤ)
  indexM_value : ∀i,denote (indexM.get i)=(i.val:ℤ)
  evaluation_value : ∀r i,denote ((evaluation.get r).get i)=(r.val:ℤ)^i.val
  interpolation_value : ∀d r,denote ((interpolation.get d).get r)=ToomCook.integerWeight (2*k-1) d r
  divisor_value : divisor=(ToomCook.commonDenominator (2*k-1)).bits

theorem exists_ROM (k : ℕ) : Nonempty (ROM k) := by
  let literal (z : ℤ) : Signed := ⟨IntegerArithmetic.ofInt z,by
    unfold Canonical
    rw [IntegerArithmetic.ofInt_correct]⟩
  refine ⟨{ base:=literal k
            indexK:=Vector.ofFn (fun i=>literal i.val)
            indexM:=Vector.ofFn (fun i=>literal i.val)
            evaluation:=Vector.ofFn (fun r=>Vector.ofFn (fun i=>literal ((r.val:ℤ)^i.val)))
            interpolation:=Vector.ofFn (fun d=>Vector.ofFn (fun r=>literal (ToomCook.integerWeight (2*k-1) d r)))
            divisor:=(ToomCook.commonDenominator (2*k-1)).bits
            base_value:=?_
            indexK_value:=?_
            indexM_value:=?_
            evaluation_value:=?_
            interpolation_value:=?_
            divisor_value:=rfl }⟩ <;>
    simp [literal,denote,IntegerArithmetic.ofInt_correct]

/-- Address multiplication and addition operate on the actual stored
binary indices. Decoding to a bounded array address is charged too. -/
def indexedRead (a : Array Signed) (i h j : Signed) : Counted Signed :=
  bind (mul i h) (fun offset=>bind (add offset j) (fun address=>
    let decoded:=decodeAddress address.val.magnitude
    let result:=readInteger a decoded.value
    ⟨result.value,decoded.operations+result.operations⟩))

def readChildArray (a : Array (Array Signed)) (r : ℕ) : Counted (Array Signed) :=
  ⟨(a[r]?).getD #[],r.size+1⟩

def shiftedRead (parts : Array (Array Signed)) (d : ℕ) (dBits hBits jBits : Signed) : Counted Signed :=
  bind (mul hBits dBits) (fun offset=>bind (negate offset) (fun negative=>
    bind (add jBits negative) (fun address=>
      if address.val.negative then ⟨zero,2⟩ else
        let decoded:=decodeAddress address.val.magnitude
        let result:=readChild parts d decoded.value
        ⟨result.value,decoded.operations+result.operations+2⟩)))

def evaluate (k h : ℕ) (rom : ROM k) (hBits : Signed) (a : Array Signed)
    (r : Fin (2*k-1)) : Counted (Array Signed) :=
  tabulateInteger h (fun _j jBits=>
    dot (fun i : Fin k=>(rom.evaluation.get r).get i)
      (fun i=>let value:=indexedRead a (rom.indexK.get i) hBits jBits
        ⟨value.value,value.operations+1⟩) (List.ofFn (id : Fin k→Fin k)))

def interpolate (k h : ℕ) (rom : ROM k) (children : Array (Array Signed)) :
    Counted (Array (Array Signed)) :=
  tabulate (2*k-1) (fun d=>tabulateInteger (2*h) (fun j _jBits=>
    bind (dot (fun r : Fin (2*k-1)=>(rom.interpolation.get d).get r)
      (fun r=>readChild children r.val j.val) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))))
      (divide rom.divisor)))

def recombine (k h : ℕ) (rom : ROM k) (hBits : Signed) (parts : Array (Array Signed)) :
    Counted (Array Signed) :=
  tabulateInteger (2*k*h) (fun _j jBits=>
    dot (fun _ : Fin (2*k-1)=>one)
      (fun d=>let value:=shiftedRead parts d.val (rom.indexM.get d) hBits jBits
        ⟨value.value,value.operations+1⟩) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))))

def power (k : ℕ) (rom : ROM k) : ℕ→ Counted Signed
  | 0 => ⟨one,1⟩
  | s+1 => bind (readConstant rom.base) (fun base=>
      bind (power k rom s) (fun previous=>bind (mul base previous) (fun z=>
        let stored:=copy z
        ⟨stored.value,stored.operations+(s+1).size+1⟩)))

/-- Complete bit-array execution. Its only coefficient arithmetic is
`normalizedAddCounted`, `normalizedMulCounted`, `normalizedDivideCounted`,
and the direct canonical sign-bit flip above. -/
def execute (k : ℕ) (rom : ROM k) : ℕ→Array Signed→Array Signed→ Counted (Array Signed)
  | 0,a,b => bind (show Counted Unit from ⟨(),1⟩) (fun _=>
      bind (readInteger a 0) (fun x=>bind (readInteger b 0) (fun y=>
        bind (mul x y) (fun z=>tabulateInteger 2 (fun j _=>
          if j.val=0 then ⟨z,1⟩ else ⟨zero,1⟩)))))
  | s+1,a,b => bind (show Counted Unit from ⟨(),(s+1).size+1⟩) (fun _=>
      bind (power k rom s) (fun length=>
        let decoded:=decodeAddress length.val.magnitude
        let h:=decoded.value
        let output:=bind (tabulate (2*k-1) (fun r=>evaluate k h rom length a r)) (fun left=>
          bind (tabulate (2*k-1) (fun r=>evaluate k h rom length b r)) (fun right=>
          bind (tabulate (2*k-1) (fun r=>
            bind (readChildArray left r.val) (fun la=>
              bind (readChildArray right r.val) (execute k rom s la)))) (fun children=>
          bind (interpolate k h rom children) (recombine k h rom length))))
        ⟨output.value,decoded.operations+output.operations⟩))

theorem dot_value {ι : Type*} (weight : ι→ Signed) (read : ι→ Counted Signed) (xs : List ι) :
    denote (dot weight read xs).value =
      (xs.map (fun i=>denote (weight i)*denote (read i).value)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [dot,bind,readConstant_value,mul_value,add_value,ih,List.map_cons,List.sum_cons]

theorem tabulateInteger_view (n : ℕ) (f : Fin n→ Signed→ Counted Signed) :
    arrayView (tabulateInteger n f).value =
      Array.ofFn (fun i=>denote (f i ((indices n).value.get i)).value) := by
  simp only [tabulateInteger,tabulate_value,bind,copy_value,arrayView,Array.map_ofFn]
  rfl

theorem power_value (k : ℕ) (rom : ROM k) (s : ℕ) :
    denote (power k rom s).value = ((k^s:ℕ):ℤ) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [power,bind,readConstant_value,copy_value,mul_value,rom.base_value,ih,
      pow_succ,Nat.cast_mul]
    ring

theorem negative_true (x : Signed) : x.val.negative=true ↔ denote x<0 := by
  rw [canonical_eq]
  simp only [IntegerArithmetic.ofInt,decide_eq_true_eq]

theorem negative_false (x : Signed) : x.val.negative=false ↔ 0≤denote x := by
  rw [canonical_eq]
  simp [IntegerArithmetic.ofInt]

theorem indexedRead_value (a : Array Signed) (i h j : ℕ) (iBits hBits jBits : Signed)
    (hi : denote iBits=(i:ℤ)) (hh : denote hBits=(h:ℤ)) (hj : denote jBits=(j:ℤ)) :
    denote (indexedRead a iBits hBits jBits).value =
      (ToomBitCost.indexedRead ToomBitCost.bitPrimitives (arrayView a) i h j).value := by
  have haddr : denote (add (mul iBits hBits).value jBits).value=((i*h+j:ℕ):ℤ) := by
    rw [add_value,mul_value,hi,hh,hj]
    push_cast
    ring
  have hd : (decodeAddress (add (mul iBits hBits).value jBits).value.val.magnitude).value=i*h+j := by
    rw [decodeMagnitude_value,haddr,Int.natAbs_natCast]
  simp only [indexedRead,bind,hd,readInteger_value,ToomBitCost.indexedRead_value
    ToomBitCost.bitPrimitives ToomBitCost.bitPrimitives_correct,ToomBitCost.readInteger]

theorem shiftedRead_value (parts : Array (Array Signed)) (d h j : ℕ)
    (dBits hBits jBits : Signed) (hd : denote dBits=(d:ℤ))
    (hh : denote hBits=(h:ℤ)) (hj : denote jBits=(j:ℤ)) :
    denote (shiftedRead parts d dBits hBits jBits).value =
      (ToomBitCost.shiftedRead ToomBitCost.bitPrimitives (childrenView parts) d h j).value := by
  let address := (add jBits (negate (mul hBits dBits).value).value).value
  have ha : denote address=(j:ℤ)-((h*d:ℕ):ℤ) := by
    dsimp [address]
    rw [add_value,negate_value,mul_value,hd,hh,hj]
    ring
  rw [ToomBitCost.shiftedRead_value _ ToomBitCost.bitPrimitives_correct]
  by_cases hs : h*d≤j
  · have hac : denote address=((j-h*d:ℕ):ℤ) := by rw [ha,Nat.cast_sub hs]
    have hn : address.val.negative=false := negative_false address |>.mpr (by rw [hac];positivity)
    have hdec : (decodeAddress address.val.magnitude).value=j-h*d := by
      rw [decodeMagnitude_value,hac,Int.natAbs_natCast]
    simp only [shiftedRead,bind]
    change denote ((if address.val.negative then (⟨zero,2⟩ : Counted Signed) else
      ⟨(readChild parts d (decodeAddress address.val.magnitude).value).value,
        (decodeAddress address.val.magnitude).operations+
          (readChild parts d (decodeAddress address.val.magnitude).value).operations+2⟩)).value = _
    simp only [hn,Bool.false_eq_true,if_false,hdec,readChild_value,if_pos hs]
  · have han : denote address<0 := by rw [ha];exact sub_neg.mpr (by exact_mod_cast (Nat.lt_of_not_ge hs))
    have hn : address.val.negative=true := (negative_true address).mpr han
    simp only [shiftedRead,bind]
    change denote ((if address.val.negative then (⟨zero,2⟩ : Counted Signed) else
      ⟨(readChild parts d (decodeAddress address.val.magnitude).value).value,
        (decodeAddress address.val.magnitude).operations+
          (readChild parts d (decodeAddress address.val.magnitude).value).operations+2⟩)).value = _
    simp only [hn,if_true,denote_zero,if_neg hs]

theorem evaluate_value (k h : ℕ) (rom : ROM k) (hBits : Signed) (hh : denote hBits=(h:ℤ))
    (a : Array Signed) (r : Fin (2*k-1)) :
    arrayView (evaluate k h rom hBits a r).value =
      (ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h (arrayView a) r).value := by
  rw [evaluate,tabulateInteger_view,ToomBitCost.evaluateCounted,ToomBitCost.tabulateInteger_value]
  congr 1
  funext j
  rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [rom.evaluation_value]
  congr 1
  exact indexedRead_value a i.val h j.val _ _ _ (rom.indexK_value i) hh (indices_value h j)

theorem interpolate_value (k h : ℕ) (rom : ROM k) (children : Array (Array Signed)) :
    childrenView (interpolate k h rom children).value =
      (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) h
        (childrenView children)).value := by
  rw [interpolate,tabulate_value,ToomBitCost.interpolateCounted,ToomBitCost.tabulateCounted_value]
  simp only [childrenView,Array.map_ofFn]
  congr 1
  funext d
  simp only [Function.comp_apply]
  rw [tabulateInteger_view,ToomBitCost.tabulateInteger_value]
  congr 1
  funext j
  simp only [bind,ToomBitCost.Counted.bind]
  let bx:=dot (fun r : Fin (2*k-1)=>(rom.interpolation.get d).get r)
    (fun r=>readChild children r.val j.val) (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
  let ix:=ToomBitCost.dotCounted ToomBitCost.bitPrimitives
    (ToomCook.integerWeight (2*k-1) d)
    (fun r : Fin (2*k-1)=>ToomBitCost.readChild (childrenView children) r.val j.val)
    (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1)))
  have hdot : denote bx.value=ix.value := by
    dsimp [bx,ix]
    rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    rw [rom.interpolation_value,readChild_value]
  change denote (divide rom.divisor bx.value).value =
    (ToomBitCost.bitPrimitives.divide (ToomCook.commonDenominator (2*k-1)) ix.value).value
  exact (divide_value (ToomCook.commonDenominator (2*k-1)) bx.value rom.divisor
    rom.divisor_value).trans (congrArg
      (fun z=>(ToomBitCost.bitPrimitives.divide (ToomCook.commonDenominator (2*k-1)) z).value) hdot)

theorem recombine_value (k h : ℕ) (rom : ROM k) (hBits : Signed) (hh : denote hBits=(h:ℤ))
    (parts : Array (Array Signed)) :
    arrayView (recombine k h rom hBits parts).value =
      (ToomBitCost.recombineCounted ToomBitCost.bitPrimitives k h (childrenView parts)).value := by
  rw [recombine,tabulateInteger_view,ToomBitCost.recombineCounted,ToomBitCost.tabulateInteger_value]
  congr 1
  funext j
  rw [dot_value,ToomBitCost.dotCounted_value _ ToomBitCost.bitPrimitives_correct]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only [denote_one]
  congr 1
  exact shiftedRead_value parts d.val h j.val _ _ _ (rom.indexM_value d) hh
    (indices_value (2*k*h) j)

theorem readChildArray_value (a : Array (Array Signed)) (r : ℕ) :
    arrayView (readChildArray a r).value = (ToomBitCost.readChildArray (childrenView a) r).value := by
  simp only [readChildArray,ToomBitCost.readChildArray,childrenView_getD]

theorem decode_power (k : ℕ) (rom : ROM k) (s : ℕ) :
    (decodeAddress (power k rom s).value.val.magnitude).value=k^s := by
  rw [decodeMagnitude_value,power_value,Int.natAbs_natCast]

theorem evaluateTable_view (k h : ℕ) (rom : ROM k) (hBits : Signed)
    (hh : denote hBits=(h:ℤ)) (a : Array Signed) :
    childrenView (tabulate (2*k-1) (fun r=>evaluate k h rom hBits a r)).value =
      (ToomBitCost.tabulateCounted (2*k-1) (fun r=>
        ToomBitCost.evaluateCounted ToomBitCost.bitPrimitives k h (arrayView a) r)).value := by
  rw [tabulate_value,ToomBitCost.tabulateCounted_value]
  simp only [childrenView,Array.map_ofFn]
  apply congrArg Array.ofFn
  funext r
  exact evaluate_value k h rom hBits hh a r

theorem execute_value (k : ℕ) (rom : ROM k) (s : ℕ) (a b : Array Signed) :
    arrayView (execute k rom s a b).value =
      (ToomBitCost.execute ToomBitCost.bitPrimitives k s (arrayView a) (arrayView b)).value := by
  induction s generalizing a b with
  | zero =>
    simp only [execute,bind,ToomBitCost.execute,ToomBitCost.Counted.bind,
      tabulateInteger_view,ToomBitCost.tabulateInteger_value]
    congr 1
    funext j
    split_ifs
    · rw [mul_value,readInteger_value,readInteger_value,ToomBitCost.bitPrimitives_correct.mul]
    · rfl
  | succ s ih =>
    have hp := power_value k rom s
    have hd := decode_power k rom s
    simp only [execute,bind,hd,ToomBitCost.execute,ToomBitCost.Counted.bind,
      ToomBitCost.powerCounted_value _ ToomBitCost.bitPrimitives_correct,
      Int.natAbs_natCast]
    rw [recombine_value k (k^s) rom _ hp]
    rw [interpolate_value]
    apply congrArg (fun children : Array (Array ℤ)=>
      (ToomBitCost.recombineCounted ToomBitCost.bitPrimitives k (k^s)
        (ToomBitCost.interpolateCounted ToomBitCost.bitPrimitives (2*k-1) (k^s) children).value).value)
    simp only [tabulate_value,ToomBitCost.tabulateCounted_value,childrenView,Array.map_ofFn]
    apply congrArg Array.ofFn
    funext r
    simp only [Function.comp_apply]
    rw [ih]
    simp only [readChildArray_value]
    apply congrArg₂ (fun a b : Array ℤ=>
      (ToomBitCost.execute ToomBitCost.bitPrimitives k s a b).value)
    · apply congrArg (fun table=>
        (ToomBitCost.readChildArray table r.val).value)
      simpa only [tabulate_value,ToomBitCost.tabulateCounted_value] using
        evaluateTable_view k (k^s) rom _ hp a
    · apply congrArg (fun table=>
        (ToomBitCost.readChildArray table r.val).value)
      simpa only [tabulate_value,ToomBitCost.tabulateCounted_value] using
        evaluateTable_view k (k^s) rom _ hp b

/-- Complete coefficient correctness for a program whose runtime inputs,
intermediates, and outputs all remain canonical signed-bit arrays. -/
theorem execute_product (k : ℕ) (rom : ROM k) (s : ℕ) (hk : 2≤k)
    (a b : Array Signed) (ha : a.size=k^s) (hb : b.size=k^s) :
    arrayView (execute k rom s a b).value =
      Array.ofFn (fun j : Fin (2*(k^s))=>
        (ToomBitCost.arrayPolynomial (arrayView a)*
          ToomBitCost.arrayPolynomial (arrayView b)).coeff j.val) := by
  rw [execute_value]
  exact ToomBitCost.execute_value ToomBitCost.bitPrimitives ToomBitCost.bitPrimitives_correct
    k s hk _ _ (by simpa only [arrayView,Array.size_map] using ha)
      (by simpa only [arrayView,Array.size_map] using hb)

end ThinMatrix.BitArraySimulation

#print axioms ThinMatrix.BitArraySimulation.add_value
#print axioms ThinMatrix.BitArraySimulation.mul_value
#print axioms ThinMatrix.BitArraySimulation.divide_value
#print axioms ThinMatrix.BitArraySimulation.divide_cost
#print axioms ThinMatrix.BitArraySimulation.negate_value
#print axioms ThinMatrix.BitArraySimulation.readInteger_cost
#print axioms ThinMatrix.BitArraySimulation.readChild_cost
#print axioms ThinMatrix.BitArraySimulation.indices_cost
#print axioms ThinMatrix.BitArraySimulation.indexedRead_value
#print axioms ThinMatrix.BitArraySimulation.shiftedRead_value
#print axioms ThinMatrix.BitArraySimulation.evaluate_value
#print axioms ThinMatrix.BitArraySimulation.interpolate_value
#print axioms ThinMatrix.BitArraySimulation.recombine_value
#print axioms ThinMatrix.BitArraySimulation.execute_value
#print axioms ThinMatrix.BitArraySimulation.execute_product
