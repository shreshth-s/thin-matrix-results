import ToomCook
import IntegerNormalization
import Mathlib.Algebra.Polynomial.OfFn

/-!
Concrete coefficient-array execution of fixed-arity Toom--Cook. This module
keeps every read, allocation/write, arithmetic call, child materialization and
recombination loop in the counted program. Arrays use random-access reads;
there are no uncharged linked-list indexing scans.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace ThinMatrix.ToomBitCost
open scoped BigOperators
open Polynomial Finset
open ThinMatrix.ToomCook
noncomputable section

/-- A depth-dependent bound used by the independent execution-cost proof. -/
def bitSlope (k : ℕ) : ℕ :=
  4*(k.size+(growthConstant k).size+(commonDenominator (2*k-1)).size+10)
def bitBudget (k s A : ℕ) : ℕ := bitSlope k*(s+1)+2*A.size+10

/-- A copied cell from the fixed read-only arity table. Evaluation powers,
Lagrange integer weights, and the common denominator are configured once
for the fixed arity, before this recursive program is run. -/
def readConstant (z : ℤ) : ToomCook.Counted ℤ := ⟨z,z.natAbs.size+1⟩


namespace Counted

def bind {α β : Type*} (x : ToomCook.Counted α) (f : α→ToomCook.Counted β) : ToomCook.Counted β :=
  let y:=f x.value
  ⟨y.value,x.operations+y.operations⟩

def pure {α : Type*} (x : α) : ToomCook.Counted α := ⟨x,0⟩
end Counted

/-- Dense polynomial view of a genuine input coefficient array. -/
def arrayPolynomial (a : Array ℤ) : ℤ[X] := ∑i : Fin a.size,C (a[i.val])*X^i.val

theorem arrayPolynomial_eq_ofFn (a : Array ℤ) :
    arrayPolynomial a=Polynomial.ofFn a.size (fun i=>a[i.val]) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [arrayPolynomial,Polynomial.C_mul_X_pow_eq_monomial]

theorem arrayPolynomial_coeff (a : Array ℤ) (j : ℕ) :
    (arrayPolynomial a).coeff j=(a[j]?).getD 0 := by
  rw [arrayPolynomial_eq_ofFn]
  by_cases hj : j<a.size
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj,Array.getElem?_eq_getElem hj];rfl
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj),
      Array.getElem?_eq_none (Nat.le_of_not_gt hj)];rfl

theorem arrayPolynomial_natDegree (a : Array ℤ) (ha : 0<a.size) :
    (arrayPolynomial a).natDegree<a.size := by
  rw [arrayPolynomial_eq_ofFn]
  exact Polynomial.ofFn_natDegree_lt (by omega) _

/-- Explicit finite tabulation, followed by one allocation and one
write per output cell. Only sequential construction uses a list. -/
def tabulateCounted {α : Type*} (n : ℕ) (f : Fin n→ToomCook.Counted α) : ToomCook.Counted (Array α) :=
  let loop:=ToomCook.Counted.sequence f (List.ofFn (id : Fin n→Fin n))
  ⟨loop.value.toArray,loop.operations+2*n⟩

theorem tabulateCounted_value {α : Type*} (n : ℕ) (f : Fin n→ToomCook.Counted α) :
    (tabulateCounted n f).value=Array.ofFn (fun i=>(f i).value) := by
  simp [tabulateCounted,ToomCook.Counted.sequence_value]

theorem tabulateCounted_operations {α : Type*} (n : ℕ) (f : Fin n→ToomCook.Counted α) :
    (tabulateCounted n f).operations=(∑i,(f i).operations)+2*n := by
  simp [tabulateCounted,ToomCook.Counted.sequence_operations_sum,List.sum_ofFn]

/-- A word read includes its value copy, address, and bounds/control
charge. These dynamic bit lengths will be bounded from actual registers. -/
def readInteger (a : Array ℤ) (i : ℕ) : ToomCook.Counted ℤ :=
  let z:=(a[i]?).getD 0
  ⟨z,z.natAbs.size+i.size+1⟩

def readChild (a : Array (Array ℤ)) (r j : ℕ) : ToomCook.Counted ℤ :=
  let child:=(a[r]?).getD #[]
  let z:=(child[j]?).getD 0
  ⟨z,z.natAbs.size+r.size+j.size+2⟩

/-- The finite signed-bit primitive interface is instantiated below
with IntegerArithmetic's explicit Boolean-list programs. -/
structure Primitives where
  add : ℤ→ℤ→ToomCook.Counted ℤ
  mul : ℤ→ℤ→ToomCook.Counted ℤ
  divide : ℕ→ℤ→ToomCook.Counted ℤ

def dotCounted {ι : Type*} (P : Primitives) (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ) :
    List ι→ToomCook.Counted ℤ
  | [] => ⟨0,1⟩
  | i::is => Counted.bind (readConstant (weight i)) (fun w=>
      Counted.bind (read i) (fun x=>
        Counted.bind (P.mul w x) (fun product=>
          Counted.bind (dotCounted P weight read is) (fun tail=>P.add product tail))))


structure PrimitivesCorrect (P : Primitives) : Prop where
  add : ∀x y,(P.add x y).value=x+y
  mul : ∀x y,(P.mul x y).value=x*y
  divide : ∀(D:ℕ)(z w:ℤ),0<D→z=(D:ℤ)*w→(P.divide D z).value=w

theorem dotCounted_value {ι : Type*} (P : Primitives) (hP : PrimitivesCorrect P)
    (weight : ι→ℤ) (read : ι→ToomCook.Counted ℤ) (xs : List ι) :
    (dotCounted P weight read xs).value=(xs.map (fun i=>weight i*(read i).value)).sum := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    simp only [dotCounted,Counted.bind,readConstant,hP.mul,hP.add,ih,List.map_cons,List.sum_cons]


/-- Instantiation by persistent canonical signed-bit algorithms. `ofInt`
is the representation relation in this integer view; the concrete programs
return those same canonical bits after a charged normalization pass. -/
def bitPrimitives : Primitives where
  add x y := let p := IntegerArithmetic.normalizedAddCounted (IntegerArithmetic.ofInt x) (IntegerArithmetic.ofInt y); ⟨IntegerArithmetic.signedValue p.1,p.2⟩
  mul x y := let p := IntegerArithmetic.normalizedMulCounted (IntegerArithmetic.ofInt x) (IntegerArithmetic.ofInt y); ⟨IntegerArithmetic.signedValue p.1,p.2⟩
  divide D z := let p := IntegerArithmetic.normalizedDivideCounted D.bits (IntegerArithmetic.ofInt z); ⟨IntegerArithmetic.signedValue p.1,p.2+D.size+1⟩

theorem bitPrimitives_correct : PrimitivesCorrect bitPrimitives where
  add x y:=by simp only [bitPrimitives,IntegerArithmetic.normalizedAddCounted_value,
    IntegerArithmetic.ofInt_correct]
  mul x y:=by simp only [bitPrimitives,IntegerArithmetic.normalizedMulCounted_value,
    IntegerArithmetic.ofInt_correct]
  divide D z w hD hz:=by
    have h:=IntegerArithmetic.normalizedDivideCounted_value D.bits
      (IntegerArithmetic.ofInt z) w (by simpa only [IntegerArithmetic.value_bits] using hD)
      (by simpa only [IntegerArithmetic.value_bits,IntegerArithmetic.ofInt_correct] using hz)
    simp only [bitPrimitives,h,IntegerArithmetic.ofInt_correct]

theorem bitPrimitive_add_cost (x y : ℤ) :
    (bitPrimitives.add x y).operations≤50*(max x.natAbs.size y.natAbs.size+1) := by
  simpa only [bitPrimitives,IntegerArithmetic.ofInt_length] using
    IntegerArithmetic.normalizedAddCounted_steps (IntegerArithmetic.ofInt x) (IntegerArithmetic.ofInt y)

theorem bitPrimitive_mul_cost (x y : ℤ) :
    (bitPrimitives.mul x y).operations≤60*(x.natAbs.size+1)*(x.natAbs.size+y.natAbs.size+2)+4 := by
  simpa only [bitPrimitives,IntegerArithmetic.ofInt_length] using
    IntegerArithmetic.normalizedMulCounted_steps (IntegerArithmetic.ofInt x) (IntegerArithmetic.ofInt y)

theorem bitPrimitive_div_cost (D : ℕ) (z : ℤ) :
    (bitPrimitives.divide D z).operations≤40*(z.natAbs.size+1)*(z.natAbs.size+D.size+1)+4 := by
  have h:=IntegerArithmetic.normalizedDivideCounted_steps D.bits (IntegerArithmetic.ofInt z)
  simp only [IntegerArithmetic.ofInt_length,Nat.size_eq_bits_len] at h
  change (IntegerArithmetic.normalizedDivideCounted D.bits (IntegerArithmetic.ofInt z)).2+D.size+1≤_
  nlinarith

/-- Literal coefficient writes charge copying the returned integer and
address/control bits, in addition to tabulation allocation. -/
def tabulateInteger (n : ℕ) (f : Fin n→ToomCook.Counted ℤ) : ToomCook.Counted (Array ℤ) :=
  tabulateCounted n (fun i=>let x:=f i;⟨x.value,x.operations+x.value.natAbs.size+i.val.size+1⟩)

theorem tabulateInteger_value (n : ℕ) (f : Fin n→ToomCook.Counted ℤ) :
    (tabulateInteger n f).value=Array.ofFn (fun i=>(f i).value) := by
  simp only [tabulateInteger,tabulateCounted_value]

theorem tabulateInteger_operations (n : ℕ) (f : Fin n→ToomCook.Counted ℤ) :
    (tabulateInteger n f).operations=
      (∑i : Fin n,((f i).operations+(f i).value.natAbs.size+i.val.size+1))+2*n := by
  simp only [tabulateInteger,tabulateCounted_operations]

/-- Address multiplication/addition also invokes the bit primitives. -/
def indexedRead (P : Primitives) (a : Array ℤ) (i h j : ℕ) : ToomCook.Counted ℤ :=
  Counted.bind (P.mul i h) (fun offset=>Counted.bind (P.add offset j)
    (fun address=>readInteger a address.natAbs))

theorem indexedRead_value (P : Primitives) (hP : PrimitivesCorrect P)
    (a : Array ℤ) (i h j : ℕ) :
    (indexedRead P a i h j).value=(a[i*h+j]?).getD 0 := by
  simp only [indexedRead,Counted.bind,hP.mul,hP.add,readInteger,
    ←Nat.cast_mul,←Nat.cast_add,Int.natAbs_natCast]

/-- Materializing a child includes the pointer/address read. -/
def readChildArray (a : Array (Array ℤ)) (r : ℕ) : ToomCook.Counted (Array ℤ) :=
  ⟨(a[r]?).getD #[],r.size+1⟩

/-- Literal evaluated coefficient table, including input reads and
all scalar operations. -/
def evaluateCounted (P : Primitives) (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) :
    ToomCook.Counted (Array ℤ) :=
  tabulateInteger h (fun j=>dotCounted P (fun i : Fin k=>(r.val:ℤ)^i.val)
    (fun i=>indexedRead P a i.val h j.val) (List.ofFn (id : Fin k→Fin k)))

/-- Literal interpolation/normalization coefficient table. Every
quotient invokes the signed bit-division program. -/
def interpolateCounted (P : Primitives) (M h : ℕ) (children : Array (Array ℤ)) :
    ToomCook.Counted (Array (Array ℤ)) :=
  tabulateCounted M (fun d=>tabulateInteger (2*h) (fun j=>
    Counted.bind (dotCounted P (integerWeight M d)
      (fun r : Fin M=>readChild children r.val j.val) (List.ofFn (id : Fin M→Fin M)))
      (P.divide (commonDenominator M))))

/-- Recombination addresses are computed by the same bit primitives;
the sign flip and sign test also have explicit charges. -/
def shiftedRead (P : Primitives) (parts : Array (Array ℤ)) (d h j : ℕ) :
    ToomCook.Counted ℤ :=
  Counted.bind (P.mul h d) (fun offset=>
    Counted.bind (show ToomCook.Counted ℤ from ⟨-offset,1⟩) (fun negOffset=>
      Counted.bind (P.add j negOffset) (fun address=>
        let result:=if 0≤address then readChild parts d address.natAbs else ⟨0,1⟩
        ⟨result.value,result.operations+address.natAbs.size+1⟩)))

theorem shiftedRead_value (P : Primitives) (hP : PrimitivesCorrect P)
    (parts : Array (Array ℤ)) (d h j : ℕ) :
    (shiftedRead P parts d h j).value=
      if h*d≤j then (readChild parts d (j-h*d)).value else 0 := by
  simp only [shiftedRead,Counted.bind,hP.mul,hP.add]
  by_cases hs:h*d≤j
  · have he : (j:ℤ)+-((h:ℤ)*d)=((j-h*d:ℕ):ℤ) := by
      rw [Nat.cast_sub hs,Nat.cast_mul];ring
    simp only [he,Int.natCast_nonneg,if_pos,Int.natAbs_natCast,hs]
  · have hj : (j:ℤ)<((h*d:ℕ):ℤ) := by exact_mod_cast (show j<h*d by omega)
    have he : (j:ℤ)+-((h:ℤ)*d)<0 := by simpa only [sub_eq_add_neg,Nat.cast_mul] using sub_neg.mpr hj
    simp only [not_le_of_gt he,if_false,hs]

/-- Every output is reconstructed by a finite shift/read/add loop. -/
def recombineCounted (P : Primitives) (k h : ℕ) (parts : Array (Array ℤ)) :
    ToomCook.Counted (Array ℤ) :=
  tabulateInteger (2*k*h) (fun j=>
    dotCounted P (fun _ : Fin (2*k-1)=>1)
      (fun d=>shiftedRead P parts d.val h j.val)
      (List.ofFn (id : Fin (2*k-1)→Fin (2*k-1))))

/-- Computing the child length uses a literal multiplication loop, rather
than an uncharged exponentiation primitive. -/
def powerCounted (P : Primitives) (k : ℕ) : ℕ→ToomCook.Counted ℤ
  | 0 => ⟨1,1⟩
  | s+1 => Counted.bind (readConstant k) (fun base=>
      Counted.bind (powerCounted P k s) (fun previous=>
        Counted.bind (P.mul base previous) (fun z=>⟨z,z.natAbs.size+(s+1).size+1⟩)))

theorem powerCounted_value (P : Primitives) (hP : PrimitivesCorrect P) (k s : ℕ) :
    (powerCounted P k s).value=(k^s:ℕ) := by
  induction s with
  | zero => simp [powerCounted]
  | succ s ih => simp only [powerCounted,Counted.bind,readConstant,hP.mul,ih,
      pow_succ,Nat.cast_mul];ring

/-- The complete finite recursive execution. All child calls are
materialized exactly once. Branch/depth control has an explicit charge,
and each child length is computed by the counted power loop. -/
def execute (P : Primitives) (k : ℕ) : ℕ→Array ℤ→Array ℤ→ToomCook.Counted (Array ℤ)
  | 0,a,b => Counted.bind (show ToomCook.Counted Unit from ⟨(),1⟩) (fun _=>
      Counted.bind (readInteger a 0) (fun x=>
      Counted.bind (readInteger b 0) (fun y=>
        Counted.bind (P.mul x y) (fun z=>tabulateInteger 2 (fun j=>
          if j.val=0 then ⟨z,1⟩ else ⟨0,1⟩)))))
  | s+1,a,b => Counted.bind (show ToomCook.Counted Unit from ⟨(),(s+1).size+1⟩) (fun _=>
      Counted.bind (powerCounted P k s) (fun length=>
    Counted.bind
      (tabulateCounted (2*k-1) (fun r=>evaluateCounted P k length.natAbs a r)) (fun left=>
    Counted.bind (tabulateCounted (2*k-1) (fun r=>evaluateCounted P k length.natAbs b r)) (fun right=>
    Counted.bind (tabulateCounted (2*k-1) (fun r=>
      Counted.bind (readChildArray left r.val) (fun la=>
        Counted.bind (readChildArray right r.val) (execute P k s la)))) (fun children=>
    Counted.bind (interpolateCounted P (2*k-1) length.natAbs children)
      (recombineCounted P k length.natAbs))))))


theorem evaluateCounted_value (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (a : Array ℤ) (r : Fin (2*k-1)) :
    (evaluateCounted P k h a r).value=
      Array.ofFn (fun j : Fin h=>(evaluatedIntegerChunk k h (arrayPolynomial a) r).coeff j.val) := by
  rw [evaluateCounted,tabulateInteger_value]
  congr 1
  funext j
  rw [dotCounted_value P hP]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq,indexedRead_value P hP]
  unfold evaluatedIntegerChunk blockPolynomial
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,←Polynomial.C_pow,Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C,ToomCook.chunk_coeff,if_pos j.isLt,arrayPolynomial_coeff]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ=>(r.val:ℤ)^i*(a[i*h+j.val]?).getD 0) k]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem interpolateCounted_value (P : Primitives) (hP : PrimitivesCorrect P)
    (M h : ℕ) (hM : 0<M) (p : (ℤ[X])[X]) (hp : p.natDegree<M)
    (children : Array (Array ℤ))
    (hchildren : ∀r : Fin M,∀j : Fin (2*h),
      (readChild children r.val j.val).value=(p.eval (C (r.val:ℤ))).coeff j.val) :
    (interpolateCounted P M h children).value=
      Array.ofFn (fun d : Fin M=>Array.ofFn (fun j : Fin (2*h)=>(p.coeff d.val).coeff j.val)) := by
  rw [interpolateCounted,tabulateCounted_value]
  congr 1
  funext d
  rw [tabulateInteger_value]
  congr 1
  funext j
  change (P.divide (commonDenominator M)
    (dotCounted P (integerWeight M d) (fun r : Fin M=>readChild children r.val j.val)
      (List.ofFn (id : Fin M→Fin M))).value).value=(p.coeff d.val).coeff j.val
  apply hP.divide
  · exact commonDenominator_pos M
  · rw [dotCounted_value P hP]
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq,hchildren]
    have hnum:=congrArg (fun q : ℤ[X]=>q.coeff j.val) (integer_interpolation_numerator M hM p hp d)
    simpa only [interpolationNumeratorPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul] using hnum


theorem divideCoefficients_natDegree_le (D : ℤ) (p : ℤ[X]) :
    (divideCoefficients D p).natDegree≤p.natDegree :=
  Polynomial.natDegree_le_natDegree (Polynomial.degree_mono (by exact Finsupp.support_mapRange))

theorem integerInterpolateCoefficient_natDegree_lt (M n : ℕ) (hn : 0<n)
    (values : Fin M→ℤ[X]) (d : Fin M) (hv : ∀r,(values r).natDegree<n) :
    (integerInterpolateCoefficient M values d).natDegree<n := by
  unfold integerInterpolateCoefficient
  apply (divideCoefficients_natDegree_le _ _).trans_lt
  unfold interpolationNumeratorPolynomial
  have h:=Polynomial.natDegree_sum_le_of_forall_le
    (fun r=>C (integerWeight M d r)*values r) (s:=Finset.univ) (n:=n-1) (by
      intro r hr
      exact Polynomial.natDegree_mul_le.trans (by simpa using (show (values r).natDegree≤n-1 by have:=hv r;omega)))
  exact h.trans_lt (by omega)

theorem arrayPolynomial_ofFn (n : ℕ) (f : ℤ[X]) (hf : f.natDegree<n) :
    arrayPolynomial (Array.ofFn (fun i : Fin n=>f.coeff i.val))=f := by
  ext j
  rw [arrayPolynomial_coeff]
  by_cases hj:j<n
  · simp [hj]
  · have hz:f.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hj,hz]

theorem readChild_ofFn_coeff (M h : ℕ) (p : Fin M→ℤ[X])
    (hp : ∀d,(p d).natDegree<2*h) (d : Fin M) (t : ℕ) :
    (readChild (Array.ofFn (fun d : Fin M=>Array.ofFn (fun j : Fin (2*h)=>(p d).coeff j.val))) d.val t).value=
      (p d).coeff t := by
  unfold readChild
  simp only [Array.getElem?_ofFn]
  by_cases ht:t<2*h
  · simp [ht]
  · have hz:(p d).coeff t=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by have:=hp d;omega)
    simp [ht,hz]

theorem recombineCounted_value (P : Primitives) (hP : PrimitivesCorrect P)
    (k h : ℕ) (p : Fin (2*k-1)→ℤ[X]) (hp : ∀d,(p d).natDegree<2*h) :
    (recombineCounted P k h (Array.ofFn (fun d : Fin (2*k-1)=>
      Array.ofFn (fun j : Fin (2*h)=>(p d).coeff j.val)))).value=
      Array.ofFn (fun j : Fin (2*k*h)=>(∑d : Fin (2*k-1),p d*X^(h*d.val)).coeff j.val) := by
  rw [recombineCounted,tabulateInteger_value]
  congr 1
  funext j
  rw [dotCounted_value P hP]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq,
    Polynomial.finsetSum_coeff,Polynomial.coeff_mul_X_pow',shiftedRead_value P hP]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hs:h*d.val≤j.val
  · simp only [if_pos hs,one_mul]
    exact readChild_ofFn_coeff (2*k-1) h p hp d (j.val-h*d.val)
  · simp [hs]

/-- Complete value correctness of the finite array execution. Every
child table is materialized and every interpolation/recombination output
is read from an actual array. -/
theorem execute_value (P : Primitives) (hP : PrimitivesCorrect P) (k s : ℕ) (hk : 2≤k)
    (a b : Array ℤ) (ha:a.size=k^s) (hb:b.size=k^s) :
    (execute P k s a b).value=Array.ofFn (fun j : Fin (2*(k^s))=>
      (arrayPolynomial a*arrayPolynomial b).coeff j.val) := by
  induction s generalizing a b with
  | zero =>
    have haf:(arrayPolynomial a).natDegree=0:=by
      have h:=arrayPolynomial_natDegree a (by rw [ha];norm_num)
      rw [ha,pow_zero] at h
      omega
    have hbf:(arrayPolynomial b).natDegree=0:=by
      have h:=arrayPolynomial_natDegree b (by rw [hb];norm_num)
      rw [hb,pow_zero] at h
      omega
    have hfa:arrayPolynomial a=C ((a[0]?).getD 0):=by
      rw [Polynomial.eq_C_of_natDegree_eq_zero haf,arrayPolynomial_coeff]
    have hfb:arrayPolynomial b=C ((b[0]?).getD 0):=by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hbf,arrayPolynomial_coeff]
    conv_rhs=>rw [hfa,hfb,←Polynomial.C_mul]
    simp only [execute,Counted.bind,readInteger,hP.mul,tabulateInteger_value]
    congr 1
    funext j
    by_cases hj:j.val=0 <;>simp only [Polynomial.coeff_C,hj,if_true,if_false]
  | succ s ih =>
    let h:=k^s
    let f:=arrayPolynomial a
    let g:=arrayPolynomial b
    let p:=blockPolynomial k h f*blockPolynomial k h g
    have hk0:0<k:=by omega
    have hh:0<h:=pow_pos hk0 _
    have hM:0<2*k-1:=by omega
    have hf:f.natDegree<k*h:=by
      have hfa:=arrayPolynomial_natDegree a (by rw [ha];positivity)
      simpa [ha,pow_succ,mul_comm,h,f] using hfa
    have hg:g.natDegree<k*h:=by
      have hga:=arrayPolynomial_natDegree b (by rw [hb];positivity)
      simpa [hb,pow_succ,mul_comm,h,g] using hga
    have hp:p.natDegree<2*k-1:=by
      have hn:=Polynomial.natDegree_mul_le (p:=blockPolynomial k h f) (q:=blockPolynomial k h g)
      have h1:=blockPolynomial_natDegree k h hk0 f
      have h2:=blockPolynomial_natDegree k h hk0 g
      dsimp [p];omega
    have hevalr (r:Fin (2*k-1)) : p.eval (C (r.val:ℤ))=
        evaluatedIntegerChunk k h f r*evaluatedIntegerChunk k h g r:=by
      dsimp [p,evaluatedIntegerChunk]
      rw [Polynomial.eval_mul]
    have hchild (r:Fin (2*k-1)) :
        (execute P k s
          (Array.ofFn (fun j:Fin h=>(evaluatedIntegerChunk k h f r).coeff j.val))
          (Array.ofFn (fun j:Fin h=>(evaluatedIntegerChunk k h g r).coeff j.val))).value=
        Array.ofFn (fun j:Fin (2*h)=>(p.eval (C (r.val:ℤ))).coeff j.val) := by
      rw [ih _ _ (by simp [h]) (by simp [h]),
        arrayPolynomial_ofFn h _ (evaluatedIntegerChunk_natDegree k h hh f r),
        arrayPolynomial_ofFn h _ (evaluatedIntegerChunk_natDegree k h hh g r)]
      rw [hevalr]
    have hvalues : ∀r:Fin (2*k-1),(p.eval (C (r.val:ℤ))).natDegree<2*h:=by
      intro r
      have hn:=Polynomial.natDegree_mul_le (p:=evaluatedIntegerChunk k h f r)
        (q:=evaluatedIntegerChunk k h g r)
      have h1:=evaluatedIntegerChunk_natDegree k h hh f r
      have h2:=evaluatedIntegerChunk_natDegree k h hh g r
      rw [hevalr]
      omega
    have hparts : ∀d:Fin (2*k-1),(p.coeff d.val).natDegree<2*h:=by
      intro d
      rw [←integerInterpolateCoefficient_correct (2*k-1) hM p hp d]
      exact integerInterpolateCoefficient_natDegree_lt _ _ (by omega) _ d hvalues
    have hinterp:=interpolateCounted_value P hP (2*k-1) h hM p hp
      (Array.ofFn (fun r:Fin (2*k-1)=>Array.ofFn (fun j:Fin (2*h)=>(p.eval (C (r.val:ℤ))).coeff j.val)))
      (fun r j=>readChild_ofFn_coeff _ h _ hvalues r j.val)
    have hrecomb:=recombineCounted_value P hP k h (fun d=>p.coeff d.val) hparts
    have heval : (∑d:Fin (2*k-1),p.coeff d.val*X^(h*d.val))=f*g:=by
      have he:p.eval (X^h)=f*g:=by
        dsimp [p]
        rw [Polynomial.eval_mul,blockPolynomial_recombine k h f hf,blockPolynomial_recombine k h g hg]
      conv_lhs=>rw [Fin.sum_univ_eq_sum_range (fun d:ℕ=>p.coeff d*X^(h*d)) (2*k-1)]
      rw [←he]
      conv_rhs=>rw [p.as_sum_range_C_mul_X_pow' hp]
      simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_pow,Polynomial.eval_X,pow_mul]
    simp only [execute,Counted.bind,powerCounted_value P hP,Int.natAbs_natCast,tabulateCounted_value,evaluateCounted_value P hP,
      readChildArray]
    simp only [Array.getElem?_ofFn]
    simp only [Fin.isLt,dif_pos,Option.getD_some]
    have hfinal : (recombineCounted P k h (interpolateCounted P (2*k-1) h
        (Array.ofFn (fun r : Fin (2*k-1)=>(execute P k s
          (Array.ofFn (fun j : Fin h=>(evaluatedIntegerChunk k h f r).coeff j.val))
          (Array.ofFn (fun j : Fin h=>(evaluatedIntegerChunk k h g r).coeff j.val))).value))).value).value=
        Array.ofFn (fun j : Fin (2*k*h)=>(f*g).coeff j.val) := by
      simp only [hchild,hinterp,hrecomb,heval]
    convert hfinal using 1
    apply Array.ext
    · simp [h,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    · intro i hi hj
      simp only [Array.getElem_ofFn,f,g]

/-- Polynomial-level result interface for cyclic folding and full-vector
arithmetic clients of the actual counted array execution. -/
theorem execute_product_correct (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (hk : 2≤k) (a b : Array ℤ)
    (ha : a.size=k^s) (hb : b.size=k^s) :
    arrayPolynomial (execute P k s a b).value=arrayPolynomial a*arrayPolynomial b := by
  have hh : 0<k^s := pow_pos (by omega) _
  have hfa:=arrayPolynomial_natDegree a (by omega)
  have hfb:=arrayPolynomial_natDegree b (by omega)
  have hp:=Polynomial.natDegree_mul_le (p:=arrayPolynomial a) (q:=arrayPolynomial b)
  rw [ha] at hfa
  rw [hb] at hfb
  rw [execute_value P hP k s hk a b ha hb]
  exact arrayPolynomial_ofFn _ _ (by omega)

theorem execute_output_size (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (hk : 2≤k) (a b : Array ℤ)
    (ha : a.size=k^s) (hb : b.size=k^s) :
    (execute P k s a b).value.size=2*(k^s) := by
  rw [execute_value P hP k s hk a b ha hb]
  exact Array.size_ofFn

#print axioms execute_product_correct
#print axioms execute_output_size

/-- Pointwise copy/address bounds for the concrete array readers. -/
theorem readInteger_cost (a : Array ℤ) (i W : ℕ)
    (hz : ((a[i]?).getD 0).natAbs.size≤W) (hi : i.size≤W) :
    (readInteger a i).operations≤2*W+1 := by
  simp only [readInteger];omega

theorem readChild_cost (a : Array (Array ℤ)) (r j W : ℕ)
    (hz : ((((a[r]?).getD #[])[j]?).getD 0).natAbs.size≤W)
    (hr : r.size≤W) (hj : j.size≤W) :
    (readChild a r j).operations≤3*W+2 := by
  simp only [readChild];omega

/-- Address computation is priced by the literal signed-bit primitives. -/
theorem indexedRead_bit_cost (a : Array ℤ) (i h j W : ℕ)
    (hi : i.size≤W) (hh : h.size≤W) (hj : j.size≤W)
    (hp : (i*h).size≤W) (ha : (i*h+j).size≤W)
    (hz : ((a[i*h+j]?).getD 0).natAbs.size≤W) :
    (indexedRead bitPrimitives a i h j).operations≤180*(W+1)^2 := by
  have hm:=bitPrimitive_mul_cost (i:ℤ) (h:ℤ)
  have hs:=bitPrimitive_add_cost ((i*h:ℕ):ℤ) (j:ℤ)
  have hr:=readInteger_cost a (i*h+j) W hz ha
  simp only [Int.natAbs_natCast] at hm hs
  have hmax : max (i*h).size j.size≤W := max_le hp hj
  have hm' : (bitPrimitives.mul i h).operations≤120*(W+1)^2+4 := by
    calc
      _≤60*(W+1)*(W+W+2)+4 := hm.trans (by gcongr)
      _=_ := by ring
  have hs' : (bitPrimitives.add ((i*h:ℕ):ℤ) j).operations≤50*(W+1) :=
    hs.trans (Nat.mul_le_mul_left 50 (by omega))
  simp only [indexedRead,Counted.bind,bitPrimitives_correct.mul,
    bitPrimitives_correct.add,←Nat.cast_mul,←Nat.cast_add,Int.natAbs_natCast]
  nlinarith [sq_nonneg (W:ℤ)]

/-- The same address bound covers subtraction, its sign branch, and the
nested coefficient read in the actual recombination loop. -/
theorem shiftedRead_bit_cost (parts : Array (Array ℤ)) (d h j W : ℕ)
    (hd : d.size≤W) (hh : h.size≤W) (hj : j.size≤W)
    (hp : (h*d).size≤W)
    (ha : ((j:ℤ)-((h*d:ℕ):ℤ)).natAbs.size≤W)
    (hz : (readChild parts d ((j:ℤ)-((h*d:ℕ):ℤ)).natAbs).value.natAbs.size≤W) :
    (shiftedRead bitPrimitives parts d h j).operations≤190*(W+1)^2 := by
  have hm:=bitPrimitive_mul_cost (h:ℤ) (d:ℤ)
  have hs:=bitPrimitive_add_cost (j:ℤ) (-((h*d:ℕ):ℤ))
  simp only [Int.natAbs_natCast,Int.natAbs_neg] at hm hs
  have hmax : max j.size (h*d).size≤W := max_le hj hp
  have hm' : (bitPrimitives.mul h d).operations≤120*(W+1)^2+4 := by
    calc
      _≤60*(W+1)*(W+W+2)+4 := hm.trans (by gcongr)
      _=_ := by ring
  have hs' : (bitPrimitives.add j (-((h*d:ℕ):ℤ))).operations≤50*(W+1) :=
    hs.trans (Nat.mul_le_mul_left 50 (by omega))
  have hr : (readChild parts d ((j:ℤ)-((h*d:ℕ):ℤ)).natAbs).operations≤3*W+2 := by
    exact readChild_cost _ _ _ W hz hd ha
  simp only [shiftedRead,Counted.bind,bitPrimitives_correct.mul,
    bitPrimitives_correct.add,←Nat.cast_mul,←sub_eq_add_neg]
  split_ifs <;> nlinarith [sq_nonneg (W:ℤ)]

/-- No exponentiation is taken as a primitive: the length power is
computed by a sequence of charged signed-bit multiplications. -/
theorem powerCounted_bit_cost (k s W : ℕ) (hk : k.size≤W)
    (hp : ∀ j ≤ s,(k^j).size≤W) (hc : ∀ j ≤ s,j.size≤W) :
    (powerCounted bitPrimitives k s).operations≤(s+1)*200*(W+1)^2 := by
  induction s with
  | zero => simp only [powerCounted];nlinarith
  | succ s ih =>
    have ht:=ih (fun j hj=>hp j (by omega)) (fun j hj=>hc j (by omega))
    have hm:=bitPrimitive_mul_cost (k:ℤ) ((k^s:ℕ):ℤ)
    have hs:=hp s (by omega)
    have hn:=hp (s+1) (by omega)
    have hd:=hc (s+1) (by omega)
    simp only [Int.natAbs_natCast] at hm
    have hm' : (bitPrimitives.mul k ((k^s:ℕ):ℤ)).operations≤120*(W+1)^2+4 := by
      calc
        _≤60*(W+1)*(W+W+2)+4 := hm.trans (by gcongr)
        _=_ := by ring
    simp only [powerCounted,Counted.bind,readConstant,
      powerCounted_value bitPrimitives bitPrimitives_correct,bitPrimitives_correct.mul,
      ←Nat.cast_mul,←pow_succ',Int.natAbs_natCast]
    nlinarith [sq_nonneg (W:ℤ)]

/-- The materialized child products used by the actual interpolation. -/
def childProducts (P : Primitives) (k s : ℕ) (a b : Array ℤ) : Array (Array ℤ) :=
  Array.ofFn (fun r : Fin (2*k-1)=>(execute P k s
    (evaluateCounted P k (k^s) a r).value
    (evaluateCounted P k (k^s) b r).value).value)

/-- Exact decomposition of the joint counter into its actual node loops,
including child-array reads and materialization. -/
theorem execute_step_operations (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (a b : Array ℤ) :
    (execute P k (s+1) a b).operations=
      (s+1).size+1+((powerCounted P k s).operations+
        (((∑r : Fin (2*k-1),(evaluateCounted P k (k^s) a r).operations)+2*(2*k-1))+
        (((∑r : Fin (2*k-1),(evaluateCounted P k (k^s) b r).operations)+2*(2*k-1))+
        (((∑r : Fin (2*k-1),(r.val.size+1+(r.val.size+1+
          (execute P k s (evaluateCounted P k (k^s) a r).value
            (evaluateCounted P k (k^s) b r).value).operations)))+2*(2*k-1))+
        ((interpolateCounted P (2*k-1) (k^s) (childProducts P k s a b)).operations+
          (recombineCounted P k (k^s)
            (interpolateCounted P (2*k-1) (k^s) (childProducts P k s a b)).value).operations))))) := by
  simp only [execute,Counted.bind,powerCounted_value P hP,Int.natAbs_natCast,
    tabulateCounted_operations,tabulateCounted_value,readChildArray,childProducts]
  simp only [Array.getElem?_ofFn]
  simp only [Fin.isLt,dif_pos,Option.getD_some]

/-- Local cost assembly uses bounds on the actual loops, rather than an
independent schedule inserted into a value-only evaluator. -/
theorem execute_step_cost_of_kernels (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (a b : Array ℤ) (E I R W B : ℕ)
    (hleft : ∀r : Fin (2*k-1),(evaluateCounted P k (k^s) a r).operations≤E)
    (hright : ∀r : Fin (2*k-1),(evaluateCounted P k (k^s) b r).operations≤E)
    (hinterp : (interpolateCounted P (2*k-1) (k^s) (childProducts P k s a b)).operations≤I)
    (hrecomb : (recombineCounted P k (k^s)
      (interpolateCounted P (2*k-1) (k^s) (childProducts P k s a b)).value).operations≤R)
    (hpower : (powerCounted P k s).operations≤W)
    (hindex : ∀r : Fin (2*k-1),r.val.size≤B) :
    (execute P k (s+1) a b).operations≤
      (∑r : Fin (2*k-1),(execute P k s (evaluateCounted P k (k^s) a r).value
        (evaluateCounted P k (k^s) b r).value).operations)+
      2*(2*k-1)*(E+B+4)+I+R+W+(s+1).size+1 := by
  have hl : (∑r : Fin (2*k-1),(evaluateCounted P k (k^s) a r).operations)≤(2*k-1)*E := by
    simpa using Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset (Fin (2*k-1))))=>hleft r)
  have hr : (∑r : Fin (2*k-1),(evaluateCounted P k (k^s) b r).operations)≤(2*k-1)*E := by
    simpa using Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset (Fin (2*k-1))))=>hright r)
  have hc : (∑r : Fin (2*k-1),(r.val.size+1+(r.val.size+1+
        (execute P k s (evaluateCounted P k (k^s) a r).value
          (evaluateCounted P k (k^s) b r).value).operations)))≤
      2*(2*k-1)*(B+1)+(∑r : Fin (2*k-1),(execute P k s
        (evaluateCounted P k (k^s) a r).value (evaluateCounted P k (k^s) b r).value).operations) := by
    calc
      _≤∑r : Fin (2*k-1),(2*(B+1)+(execute P k s
          (evaluateCounted P k (k^s) a r).value (evaluateCounted P k (k^s) b r).value).operations) :=
        Finset.sum_le_sum (fun r _=>by have:=hindex r;omega)
      _=_ := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring
  rw [execute_step_operations P hP]
  nlinarith

/-- Base multiplication also includes its reads, canonical scalar product,
allocation, output copies, and branch control. -/
theorem execute_zero_bit_cost (a b : Array ℤ) (W : ℕ) (hW : 1≤W)
    (ha : ((a[0]?).getD 0).natAbs.size≤W)
    (hb : ((b[0]?).getD 0).natAbs.size≤W)
    (hz : (((a[0]?).getD 0)*((b[0]?).getD 0)).natAbs.size≤W) :
    (execute bitPrimitives k 0 a b).operations≤150*(W+1)^2 := by
  let z:=((a[0]?).getD 0)*((b[0]?).getD 0)
  have hm:=bitPrimitive_mul_cost ((a[0]?).getD 0) ((b[0]?).getD 0)
  have hm' : (bitPrimitives.mul ((a[0]?).getD 0) ((b[0]?).getD 0)).operations≤
      120*(W+1)^2+4 := by
    calc
      _≤60*(W+1)*(W+W+2)+4 := hm.trans (by gcongr)
      _=_ := by ring
  have ht : (tabulateInteger 2 (fun j : Fin 2=>
      if j.val=0 then (⟨z,1⟩:ToomCook.Counted ℤ) else ⟨0,1⟩)).operations≤4*W+8 := by
    rw [tabulateInteger_operations]
    have hs : (∑j : Fin 2,((if j.val=0 then (⟨z,1⟩:ToomCook.Counted ℤ) else ⟨0,1⟩).operations+
        (if j.val=0 then (⟨z,1⟩:ToomCook.Counted ℤ) else ⟨0,1⟩).value.natAbs.size+j.val.size+1))≤
        2*(2*W+2) := by
      calc
        _≤∑_j : Fin 2,(2*W+2) := Finset.sum_le_sum (fun j _=>by
          have hj : j.val.size≤W := by
            have hle : j.val≤1 := by omega
            exact (Nat.size_le_size hle).trans (by simpa using hW)
          by_cases he:j.val=0
          · simp only [if_pos he];change 1+z.natAbs.size+j.val.size+1≤_;dsimp [z];omega
          · simp only [if_neg he];norm_num;omega)
        _=_ := by simp
    omega
  simp only [execute,Counted.bind,bitPrimitives_correct.mul]
  change 1+((readInteger a 0).operations+((readInteger b 0).operations+
    ((bitPrimitives.mul ((a[0]?).getD 0) ((b[0]?).getD 0)).operations+
      (tabulateInteger 2 (fun j : Fin 2=>if j.val=0 then ⟨z,1⟩ else ⟨0,1⟩)).operations)))≤_
  have hr1 : (readInteger a 0).operations≤W+1 := by simp only [readInteger];simpa using Nat.add_le_add_right ha 1
  have hr2 : (readInteger b 0).operations≤W+1 := by simp only [readInteger];simpa using Nat.add_le_add_right hb 1
  nlinarith [sq_nonneg (W:ℤ)]

/-- Genuine product of the two block polynomials at a recursive node. -/
def nodePolynomial (k s : ℕ) (f g : ℤ[X]) : (ℤ[X])[X] :=
  blockPolynomial k (k^s) f*blockPolynomial k (k^s) g

theorem nodePolynomial_natDegree (k s : ℕ) (hk : 2≤k) (f g : ℤ[X]) :
    (nodePolynomial k s f g).natDegree<2*k-1 := by
  have h1:=blockPolynomial_natDegree k (k^s) (by omega) f
  have h2:=blockPolynomial_natDegree k (k^s) (by omega) g
  have hn:=Polynomial.natDegree_mul_le (p:=blockPolynomial k (k^s) f)
    (q:=blockPolynomial k (k^s) g)
  dsimp [nodePolynomial];omega

theorem nodeEvaluation_eq (k s : ℕ) (f g : ℤ[X]) (r : Fin (2*k-1)) :
    (nodePolynomial k s f g).eval (C (r.val:ℤ))=
      evaluatedIntegerChunk k (k^s) f r*evaluatedIntegerChunk k (k^s) g r := by
  simp only [nodePolynomial,Polynomial.eval_mul,evaluatedIntegerChunk]

theorem nodeEvaluation_natDegree (k s : ℕ) (hk : 2≤k) (f g : ℤ[X])
    (r : Fin (2*k-1)) :
    ((nodePolynomial k s f g).eval (C (r.val:ℤ))).natDegree<2*(k^s) := by
  have hh:0<k^s:=pow_pos (by omega) _
  rw [nodeEvaluation_eq]
  have h1:=evaluatedIntegerChunk_natDegree k (k^s) hh f r
  have h2:=evaluatedIntegerChunk_natDegree k (k^s) hh g r
  have hn:=Polynomial.natDegree_mul_le (p:=evaluatedIntegerChunk k (k^s) f r)
    (q:=evaluatedIntegerChunk k (k^s) g r)
  omega

theorem nodeEvaluation_bound (k s : ℕ) (hk : 2≤k) (f g : ℤ[X]) (A : ℕ)
    (hf : CoeffBound f (A:ℤ)) (hg : CoeffBound g (A:ℤ)) (r : Fin (2*k-1)) :
    CoeffBound ((nodePolynomial k s f g).eval (C (r.val:ℤ)))
      (((k^s:ℕ):ℤ)*((growthConstant k:ℤ)*(A:ℤ))^2) := by
  have hh:0<k^s:=pow_pos (by omega) _
  rw [nodeEvaluation_eq]
  exact product_coefficient_bound _ _ (k^s) _ (by positivity)
    (evaluatedIntegerChunk_natDegree k (k^s) hh f r)
    (evaluatedIntegerChunk_bound k (k^s) f r (A:ℤ) (by positivity) hf)
    (evaluatedIntegerChunk_bound k (k^s) g r (A:ℤ) (by positivity) hg)

/-- Each exact interpolation output is bounded by its genuine integer
numerator; positivity of the fixed common denominator prevents growth. -/
theorem nodeCoefficient_bound (k s : ℕ) (hk : 2≤k) (f g : ℤ[X]) (A : ℕ)
    (hf : CoeffBound f (A:ℤ)) (hg : CoeffBound g (A:ℤ)) (d : Fin (2*k-1)) :
    CoeffBound ((nodePolynomial k s f g).coeff d.val)
      ((k^s*(growthConstant k)^3*A^2:ℕ):ℤ) := by
  let p:=nodePolynomial k s f g
  have hp:p.natDegree<2*k-1:=nodePolynomial_natDegree k s hk f g
  have hnum:=interpolationNumeratorPolynomial_bound k
    (fun r=>(p.eval (C (r.val:ℤ)))) d
    (((k^s:ℕ):ℤ)*((growthConstant k:ℤ)*(A:ℤ))^2) (by positivity)
    (fun r=>nodeEvaluation_bound k s hk f g A hf hg r)
  have he:=integer_interpolation_numerator (2*k-1) (by omega) p hp d
  rw [he] at hnum
  have hD : (1:ℤ)≤commonDenominator (2*k-1) := by
    exact_mod_cast commonDenominator_pos (2*k-1)
  intro j
  have hn:=hnum j
  simp only [Polynomial.coeff_C_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at hn
  have hsmall : |(p.coeff d.val).coeff j|≤
      (commonDenominator (2*k-1):ℤ)*|(p.coeff d.val).coeff j| := by
    nlinarith [abs_nonneg ((p.coeff d.val).coeff j)]
  apply hsmall.trans
  convert hn using 1 <;> push_cast <;> first | ring | rfl

/-- The interpolation child table is the actual materialized execution
array, with its exact polynomial interpretation. -/
theorem childProducts_value (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (hk : 2≤k) (a b : Array ℤ) :
    childProducts P k s a b=Array.ofFn (fun r : Fin (2*k-1)=>
      Array.ofFn (fun j : Fin (2*(k^s))=>
        ((nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b)).eval (C (r.val:ℤ))).coeff j.val)) := by
  unfold childProducts
  congr 1
  funext r
  rw [evaluateCounted_value P hP,evaluateCounted_value P hP]
  rw [execute_value P hP k s hk _ _ (by simp) (by simp)]
  have hh:0<k^s:=pow_pos (by omega) _
  rw [arrayPolynomial_ofFn _ _ (evaluatedIntegerChunk_natDegree k (k^s) hh (arrayPolynomial a) r),
    arrayPolynomial_ofFn _ _ (evaluatedIntegerChunk_natDegree k (k^s) hh (arrayPolynomial b) r),
    nodeEvaluation_eq]

theorem nodeCoefficient_natDegree (k s : ℕ) (hk : 2≤k) (f g : ℤ[X])
    (d : Fin (2*k-1)) :
    ((nodePolynomial k s f g).coeff d.val).natDegree<2*(k^s) := by
  have hp:=nodePolynomial_natDegree k s hk f g
  rw [←integerInterpolateCoefficient_correct (2*k-1) (by omega)
    (nodePolynomial k s f g) hp d]
  exact integerInterpolateCoefficient_natDegree_lt _ _ (by positivity) _ d
    (fun r=>nodeEvaluation_natDegree k s hk f g r)

theorem interpolate_childProducts_value (P : Primitives) (hP : PrimitivesCorrect P)
    (k s : ℕ) (hk : 2≤k) (a b : Array ℤ) :
    (interpolateCounted P (2*k-1) (k^s) (childProducts P k s a b)).value=
      Array.ofFn (fun d : Fin (2*k-1)=>Array.ofFn (fun j : Fin (2*(k^s))=>
        ((nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b)).coeff d.val).coeff j.val)) := by
  rw [childProducts_value P hP k s hk a b]
  apply interpolateCounted_value P hP (2*k-1) (k^s) (by omega)
    (nodePolynomial k s (arrayPolynomial a) (arrayPolynomial b))
    (nodePolynomial_natDegree k s hk _ _)
  intro r j
  exact readChild_ofFn_coeff _ _ _ (fun r=>nodeEvaluation_natDegree k s hk _ _ r) r j.val

set_option maxHeartbeats 800000 in
theorem kernel_assembly_numeric (k h W s : ℕ)
    (hk : 2 ≤ k) (hh : 1 ≤ h) (hW : 1 ≤ W) (hs : s+1 ≤ W) :
    let M := 2*k-1
    let u := W+1
    let E := h*(k*(180*u^2+150*u^2)+2*W+4)
    let I := M*(2*h*(M*((3*W+2)+150*u^2)+80*u^2+2*W+8)+2)
    let R := 2*k*h*(M*(190*u^2+150*u^2)+2*W+4)
    2*M*(E+W+4)+I+R+200*(s+1)*u^2+u
      ≤ 10000*(k+1)^4*k*h*u^3 := by
  dsimp only
  calc
    _ ≤ 2*(2*k-1)*(h*(k*(180*(W+1)^2+150*(W+1)^2)+2*W+4)+W+4)
      +(2*k-1)*(2*h*((2*k-1)*((3*W+2)+150*(W+1)^2)+80*(W+1)^2+2*W+8)+2)
      +2*k*h*((2*k-1)*(190*(W+1)^2+150*(W+1)^2)+2*W+4)
      +200*W*(W+1)^2+(W+1) := by gcongr
    _ ≤ _ := by
      obtain ⟨a, rfl⟩ : ∃ a, k = a+2 := ⟨k-2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, W = b+1 := ⟨W-1, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, h = c+1 := ⟨h-1, by omega⟩
      have hm : 2*(a+2)-1 = 2*a+3 := by omega
      rw [hm]
      ring_nf
      omega

theorem kernel_assembly_charged (k h W s power control : ℕ)
    (hk : 2 ≤ k) (hh : 1 ≤ h) (hW : 1 ≤ W) (hs : s+1 ≤ W)
    (hp : power≤200*(s+1)*(W+1)^2) (hc : control≤W+1) :
    let M := 2*k-1
    let u := W+1
    let E := h*(k*(180*u^2+150*u^2)+2*W+4)
    let I := M*(2*h*(M*((3*W+2)+150*u^2)+80*u^2+2*W+8)+2)
    let R := 2*k*h*(M*(190*u^2+150*u^2)+2*W+4)
    2*M*(E+W+4)+I+R+power+control
      ≤ 10000*(k+1)^4*k*h*u^3 := by
  have hn:=kernel_assembly_numeric k h W s hk hh hW hs
  dsimp only at hn ⊢
  omega

theorem kernel_assembly_padded (k W s power control : ℕ)
    (hk : 2 ≤ k) (hW : 1 ≤ W) (hs : s+1 ≤ W)
    (hp : power≤200*(s+1)*(W+1)^2) (hc : control≤W+1) :
    let M := 2*k-1
    let u := W+1
    let h := k^s
    let E := h*(k*(180*u^2+150*u^2)+2*W+4)
    let I := M*(2*h*(M*((3*W+2)+150*u^2)+80*u^2+2*W+8)+2)
    let R := 2*k*h*(M*(190*u^2+150*u^2)+2*W+4)
    2*M*(E+W+4)+I+R+power+control
      ≤ 10000*(k+1)^4*k*h*u^3 :=
  kernel_assembly_charged k (k^s) W s power control hk
    (Nat.one_le_pow s k (by omega)) hW hs hp hc

#print axioms kernel_assembly_numeric
#print axioms kernel_assembly_charged
#print axioms kernel_assembly_padded


#print axioms nodeEvaluation_bound
#print axioms nodeCoefficient_bound
#print axioms childProducts_value
#print axioms interpolate_childProducts_value

#print axioms execute_zero_bit_cost

#print axioms execute_step_operations
#print axioms execute_step_cost_of_kernels

#print axioms indexedRead_bit_cost
#print axioms shiftedRead_bit_cost
#print axioms powerCounted_bit_cost

#print axioms execute_value
#print axioms recombineCounted_value
#print axioms evaluateCounted_value
#print axioms interpolateCounted_value
#print axioms tabulateCounted_operations
end
end ThinMatrix.ToomBitCost
