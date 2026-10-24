import IntegerArithmetic

/-!
# Persistent canonical signed-bit arithmetic

This module refines the Boolean-list programs in IntegerArithmetic with
concrete reverse/drop/reverse normalization. Normalization removes false
most-significant bits and clears the sign of zero, without interpreting a
list as an unbounded integer during execution.

The counted evaluators store each recursive child once. Their counters use the
same bit-serial instruction model as IntegerArithmetic: counters are ghost
annotations, and the bridge to the project's word machine remains separate.
The normalization charge is linear in the raw output-list length; it is not a
claim of a bound in the possibly much shorter canonical output length.
-/

namespace ThinMatrix.IntegerArithmetic

def normalize (bs : List Bool) : List Bool := bs.rdropWhile (fun b => !b)
theorem value_append_false (bs : List Bool) : value (bs++[false])=value bs := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih => simp only [List.cons_append,value,ih]
theorem value_append_true_pos (bs : List Bool) : 0<value (bs++[true]) := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih => simp only [List.cons_append,value]; omega
theorem bits_value_append_true (bs : List Bool) : (value (bs++[true])).bits=bs++[true] := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    have ht : value (bs++[true])≠0 := Nat.ne_of_gt (value_append_true_pos bs)
    cases b with
    | false =>
      simp only [List.cons_append,value,digit_false,zero_add]
      rw [Nat.bit0_bits _ ht,ih]
    | true =>
      simp only [List.cons_append,value,digit_true]
      rw [Nat.add_comm 1 _,Nat.bit1_bits,ih]
theorem normalize_eq_bits (bs : List Bool) : normalize bs=(value bs).bits := by
  induction bs using List.reverseRecOn with
  | nil => simp [normalize,value]
  | append_singleton bs b ih =>
    cases b with
    | false => simpa [normalize,List.rdropWhile_concat,value_append_false] using ih
    | true => simpa [normalize,List.rdropWhile_concat] using (bits_value_append_true bs).symm
theorem normalize_value (bs : List Bool) : value (normalize bs)=value bs := by
  rw [normalize_eq_bits,value_bits]
theorem normalize_length (bs : List Bool) : (normalize bs).length≤bs.length :=
  (List.rdropWhile_prefix (fun b : Bool=>!b) bs).length_le
theorem normalize_eq_nil_iff (bs : List Bool) : normalize bs=[] ↔ value bs=0 := by
  constructor
  · intro h
    have hv := congrArg value h
    rw [normalize_value] at hv
    simpa [value] using hv
  · intro h
    simp [normalize_eq_bits,h]

def normalizeSigned (x : SignedBits) : SignedBits :=
  let bs:=normalize x.magnitude
  if bs=[] then ⟨false,[]⟩ else ⟨x.negative,bs⟩

theorem normalizeSigned_value (x : SignedBits) :
    signedValue (normalizeSigned x)=signedValue x := by
  cases x with
  | mk n m =>
    by_cases hn : normalize m=[]
    · have hz := (normalize_eq_nil_iff m).mp hn
      cases n <;> simp [normalizeSigned,hn,signedValue,hz,value]
    · cases n <;> simp [normalizeSigned,hn,signedValue,normalize_value]

theorem normalizeSigned_eq_ofInt (x : SignedBits) :
    normalizeSigned x=ofInt (signedValue x) := by
  cases x with
  | mk n m =>
    by_cases hz : value m=0
    · have hn := (normalize_eq_nil_iff m).mpr hz
      cases n <;> simp [normalizeSigned,hn,ofInt,signedValue,hz]
    · have hn : normalize m≠[] := fun h=>hz ((normalize_eq_nil_iff m).mp h)
      cases n with
      | false =>
        simp only [normalizeSigned,hn,if_false]
        simp [ofInt,signedValue,normalize_eq_bits,Int.not_lt.mpr (Int.natCast_nonneg _)]
      | true =>
        simp only [normalizeSigned,hn,if_false]
        simp [ofInt,signedValue,normalize_eq_bits,Nat.pos_of_ne_zero hz]

def reverseLoopCounted : List Bool → List Bool → List Bool × ℕ
  | [],acc => (acc,1)
  | b::bs,acc =>
      let t:=reverseLoopCounted bs (b::acc)
      (t.1,t.2+3)

theorem reverseLoopCounted_value (bs acc : List Bool) :
    (reverseLoopCounted bs acc).1=bs.reverse++acc := by
  induction bs generalizing acc with
  | nil => simp [reverseLoopCounted]
  | cons b bs ih =>
    simp [reverseLoopCounted,ih,List.reverse_cons,List.append_assoc]

theorem reverseLoopCounted_steps (bs acc : List Bool) :
    (reverseLoopCounted bs acc).2=3*bs.length+1 := by
  induction bs generalizing acc with
  | nil => simp [reverseLoopCounted]
  | cons b bs ih => simp [reverseLoopCounted,ih];omega

def dropFalseCounted : List Bool → List Bool × ℕ
  | [] => ([],1)
  | false::bs =>
      let t:=dropFalseCounted bs
      (t.1,t.2+2)
  | true::bs => (true::bs,1)

theorem dropFalseCounted_value (bs : List Bool) :
    (dropFalseCounted bs).1=bs.dropWhile (fun b=>!b) := by
  induction bs with
  | nil => simp [dropFalseCounted]
  | cons b bs ih => cases b <;> simp [dropFalseCounted,ih]

theorem dropFalseCounted_steps (bs : List Bool) :
    (dropFalseCounted bs).2≤2*bs.length+1 := by
  induction bs with
  | nil => simp [dropFalseCounted]
  | cons b bs ih =>
    cases b with
    | false => simp only [dropFalseCounted,List.length_cons];omega
    | true => simp [dropFalseCounted]

def normalizeCounted (bs : List Bool) : List Bool × ℕ :=
  let r:=reverseLoopCounted bs []
  let d:=dropFalseCounted r.1
  let n:=reverseLoopCounted d.1 []
  (n.1,r.2+d.2+n.2+2)

theorem normalizeCounted_value (bs : List Bool) :
    (normalizeCounted bs).1=normalize bs := by
  simp only [normalizeCounted,reverseLoopCounted_value,
    List.append_nil,dropFalseCounted_value,normalize,List.rdropWhile]

theorem normalizeCounted_steps (bs : List Bool) :
    (normalizeCounted bs).2≤8*bs.length+5 := by
  have hd := dropFalseCounted_steps bs.reverse
  have hl := List.length_dropWhile_le (fun b : Bool=>!b) bs.reverse
  simp only [List.length_reverse] at hd hl
  simp only [normalizeCounted,reverseLoopCounted_steps,
    reverseLoopCounted_value,List.append_nil,dropFalseCounted_value]
  omega

def normalizeSignedCounted (x : SignedBits) : SignedBits × ℕ :=
  let t:=normalizeCounted x.magnitude
  (if t.1=[] then ⟨false,[]⟩ else ⟨x.negative,t.1⟩,t.2+3)

theorem normalizeSignedCounted_value (x : SignedBits) :
    (normalizeSignedCounted x).1=ofInt (signedValue x) := by
  rw [←normalizeSigned_eq_ofInt]
  simp only [normalizeSignedCounted,normalizeCounted_value,normalizeSigned]

theorem normalizeSignedCounted_steps (x : SignedBits) :
    (normalizeSignedCounted x).2≤8*x.magnitude.length+8 := by
  have h:=normalizeCounted_steps x.magnitude
  simp only [normalizeSignedCounted]
  omega

/-- Normalize a concrete arithmetic result before persistent storage. -/
def normalizeResult (raw : SignedBits × ℕ) : SignedBits × ℕ :=
  let result:=normalizeSignedCounted raw.1
  (result.1,raw.2+result.2)

theorem normalizeResult_value (raw : SignedBits × ℕ) :
    (normalizeResult raw).1=ofInt (signedValue raw.1) := by
  simp only [normalizeResult,normalizeSignedCounted_value]

theorem normalizeResult_steps (raw : SignedBits × ℕ) :
    (normalizeResult raw).2≤raw.2+8*raw.1.magnitude.length+8 := by
  have h:=normalizeSignedCounted_steps raw.1
  simp only [normalizeResult]
  omega

def normalizedAddCounted (x y : SignedBits) : SignedBits × ℕ :=
  normalizeResult (signedAddCounted x y)

theorem normalizedAddCounted_value (x y : SignedBits) :
    (normalizedAddCounted x y).1=ofInt (signedValue x+signedValue y) := by
  rw [normalizedAddCounted,normalizeResult_value,
    (signedAddCounted_projections x y).1,signedAdd_correct]

theorem normalizedAddCounted_steps (x y : SignedBits) :
    (normalizedAddCounted x y).2≤
      50*(max x.magnitude.length y.magnitude.length+1) := by
  have h:=normalizeResult_steps (signedAddCounted x y)
  rw [(signedAddCounted_projections x y).1,
    (signedAddCounted_projections x y).2] at h
  have hc:=signedAddSteps_bound x y
  have hl:=signedAdd_length x y
  change (normalizeResult (signedAddCounted x y)).2≤_
  omega

def normalizedMulCounted (x y : SignedBits) : SignedBits × ℕ :=
  normalizeResult (signedMulCounted x y)

theorem normalizedMulCounted_value (x y : SignedBits) :
    (normalizedMulCounted x y).1=ofInt (signedValue x*signedValue y) := by
  rw [normalizedMulCounted,normalizeResult_value,
    (signedMulCounted_projections x y).1,signedMul_correct]

theorem normalizedMulCounted_steps (x y : SignedBits) :
    (normalizedMulCounted x y).2≤
      60*(x.magnitude.length+1)*(x.magnitude.length+y.magnitude.length+2)+4 := by
  have h:=normalizeResult_steps (signedMulCounted x y)
  rw [(signedMulCounted_projections x y).1,
    (signedMulCounted_projections x y).2] at h
  have hc:=signedMulSteps_bound x y
  have hl : (signedMul x y).magnitude.length≤
      2*x.magnitude.length+y.magnitude.length+1 := by
    exact mulBits_length x.magnitude y.magnitude
  change (normalizeResult (signedMulCounted x y)).2≤_
  nlinarith

def normalizedDivideCounted (divisor : List Bool) (x : SignedBits) : SignedBits × ℕ :=
  normalizeResult (signedDivideCounted divisor x)

theorem normalizedDivideCounted_value (divisor : List Bool) (x : SignedBits) (w : ℤ)
    (hD : 0<value divisor) (hz : signedValue x=(value divisor:ℤ)*w) :
    (normalizedDivideCounted divisor x).1=ofInt w := by
  rw [normalizedDivideCounted,normalizeResult_value,
    (signedDivideCounted_projections divisor x).1,
    signedDivide_exact divisor x w hD hz]

theorem normalizedDivideCounted_steps (divisor : List Bool) (x : SignedBits) :
    (normalizedDivideCounted divisor x).2≤
      30*(x.magnitude.length+1)*(x.magnitude.length+divisor.length+1)+4 := by
  have h:=normalizeResult_steps (signedDivideCounted divisor x)
  rw [(signedDivideCounted_projections divisor x).1,
    (signedDivideCounted_projections divisor x).2] at h
  have hc:=signedDivideSteps_bound divisor x
  have hl : (signedDivide divisor x).magnitude.length=x.magnitude.length :=
    divideBits_quotient_length divisor x.magnitude
  change (normalizeResult (signedDivideCounted divisor x)).2≤_
  nlinarith

#print axioms normalize_eq_bits
#print axioms normalize_value
#print axioms normalize_length
#print axioms normalizeSigned_eq_ofInt
#print axioms normalizeSignedCounted_value
#print axioms normalizeSignedCounted_steps
#print axioms normalizeResult_value
#print axioms normalizeResult_steps
#print axioms normalizedAddCounted_value
#print axioms normalizedAddCounted_steps
#print axioms normalizedMulCounted_value
#print axioms normalizedMulCounted_steps
#print axioms normalizedDivideCounted_value
#print axioms normalizedDivideCounted_steps

end ThinMatrix.IntegerArithmetic
