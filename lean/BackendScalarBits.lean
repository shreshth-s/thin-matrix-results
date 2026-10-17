import IntegerArithmetic
import CacheDenseLowering
import PipelineBitBounds

/-!
# Binary primitive prices for the stored thin-product backend

The primitive execution model stores signed binary lists in coefficient cells.
These lemmas price actual bit-list add, subtract, schoolbook multiply, and
long division, plus explicit payload copying. Native Int values below are
semantic projections of those cells, not an assumption that conversion from
an arbitrary opaque Int to its binary list is free.

This module supplies local arithmetic adapters and missing width bridges.
Instantiating every native backend operation by this model, and compiling
array addressing to the target RAM, remain separate operational refinements.
-/
namespace ThinMatrix.BackendScalarBits
open IntegerArithmetic
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- One common polynomial price for every scalar bit-list primitive. -/
def scalarUnit (B : ℕ) : ℕ := 100*(B+1)^2

/-- Includes payload bits and the address bits exposed by an indexed cell
interface. No constant-time arbitrary-size integer arithmetic is assumed. -/
def addressedUnit (B addressBits : ℕ) : ℕ := scalarUnit (B+addressBits+1)

theorem add_price (B : ℕ) (x y : SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (signedAddCounted x y).2 ≤ scalarUnit B := by
  rw [(signedAddCounted_projections x y).2]
  have h := signedAddSteps_bound x y
  have hm : max x.magnitude.length y.magnitude.length ≤ B := max_le hx hy
  unfold scalarUnit
  nlinarith

def subtractCounted (x y : SignedBits) : SignedBits × ℕ :=
  let result := signedAddCounted x (signedNeg y)
  (result.1,result.2+1)

theorem subtract_correct (x y : SignedBits) :
    signedValue (subtractCounted x y).1 = signedValue x-signedValue y := by
  rw [subtractCounted,(signedAddCounted_projections _ _).1,signedAdd_correct,signedNeg_correct]
  ring

theorem subtract_price (B : ℕ) (x y : SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (subtractCounted x y).2 ≤ scalarUnit B := by
  have h := signedAddSteps_bound x (signedNeg y)
  have hm : max x.magnitude.length (signedNeg y).magnitude.length ≤ B := max_le hx hy
  simp only [subtractCounted,(signedAddCounted_projections _ _).2]
  unfold scalarUnit
  nlinarith

theorem multiply_price (B : ℕ) (x y : SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (signedMulCounted x y).2 ≤ scalarUnit B := by
  rw [(signedMulCounted_projections x y).2]
  have h := signedMulSteps_bound x y
  have hm : 40*(x.magnitude.length+1)*(x.magnitude.length+y.magnitude.length+2)+4 ≤
      40*(B+1)*(2*B+2)+4 := by gcongr; omega
  unfold scalarUnit
  nlinarith

theorem divide_price (B : ℕ) (D : List Bool) (x : SignedBits)
    (hx : x.magnitude.length ≤ B) (hD : D.length ≤ B) :
    (signedDivideCounted D x).2 ≤ scalarUnit B := by
  rw [(signedDivideCounted_projections D x).2]
  have h := signedDivideSteps_bound D x
  have hm : 20*(x.magnitude.length+1)*(x.magnitude.length+D.length+1)+4 ≤
      20*(B+1)*(2*B+1)+4 := by gcongr; omega
  unfold scalarUnit
  nlinarith

theorem exact_divide_correct (D : List Bool) (x : SignedBits) (w : ℤ)
    (hD : 0 < value D) (hx : signedValue x = (value D : ℤ)*w) :
    signedValue (signedDivideCounted D x).1 = w := by
  rw [(signedDivideCounted_projections D x).1]
  exact signedDivide_exact D x w hD hx

/-- Literal bit copying, with one read and one write per bit. -/
def copyBits : List Bool → List Bool × ℕ
  | [] => ([],1)
  | b::bs => let child := copyBits bs; (b::child.1,child.2+2)

@[simp] theorem copyBits_value (bs : List Bool) : (copyBits bs).1 = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [copyBits,ih]

@[simp] theorem copyBits_work (bs : List Bool) : (copyBits bs).2 = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [copyBits,ih]; omega

def copyCell (x : SignedBits) : SignedBits × ℕ :=
  let data := copyBits x.magnitude
  (⟨x.negative,data.1⟩,data.2+1)

@[simp] theorem copyCell_value (x : SignedBits) : (copyCell x).1 = x := by simp [copyCell]

theorem copyCell_price (B : ℕ) (x : SignedBits) (hx : x.magnitude.length ≤ B) :
    (copyCell x).2 ≤ scalarUnit B := by
  simp only [copyCell,copyBits_work]
  unfold scalarUnit
  nlinarith

/-- Nat loop/index division is also the proved binary long-division program. -/
theorem unsigned_divide_price (B : ℕ) (D x : List Bool)
    (hx : x.length ≤ B) (hD : D.length ≤ B) :
    (divideCounted D x).2 ≤ scalarUnit B := by
  rw [(divideCounted_projections D x).2]
  have h := divideSteps_bound D x
  have hm : 20*(x.length+1)*(x.length+D.length+1) ≤ 20*(B+1)*(2*B+1) := by gcongr; omega
  unfold scalarUnit
  nlinarith

/-- Input bit widths bound the transient product representation as well. -/
theorem multiply_output_width (B : ℕ) (x y : SignedBits)
    (hx : x.magnitude.length ≤ B) (hy : y.magnitude.length ≤ B) :
    (signedMulCounted x y).1.magnitude.length ≤ 3*B+1 := by
  rw [(signedMulCounted_projections x y).1]
  exact (mulBits_length x.magnitude y.magnitude).trans (by omega)

/-- The canonical Int wrappers carry exactly the same primitive prices;
these wrappers are semantic binary-input/output specifications. -/
theorem int_add_price (B : ℕ) (z w : ℤ)
    (hz : z.natAbs.size ≤ B) (hw : w.natAbs.size ≤ B) :
    (signedAddIntCounted z w).2 ≤ scalarUnit B := by
  exact add_price B (ofInt z) (ofInt w) (by simpa only [ofInt_length] using hz)
    (by simpa only [ofInt_length] using hw)

theorem int_multiply_price (B : ℕ) (z w : ℤ)
    (hz : z.natAbs.size ≤ B) (hw : w.natAbs.size ≤ B) :
    (signedMulIntCounted z w).2 ≤ scalarUnit B := by
  exact multiply_price B (ofInt z) (ofInt w) (by simpa only [ofInt_length] using hz)
    (by simpa only [ofInt_length] using hw)

theorem int_exact_divide_price (B D : ℕ) (z : ℤ)
    (hz : z.natAbs.size ≤ B) (hD : D.size ≤ B) :
    (binaryExactDivCounted D z).2 ≤ scalarUnit B := by
  exact divide_price B D.bits (ofInt z) (by simpa only [ofInt_length] using hz)
    (by simpa only [Nat.size_eq_bits_len] using hD)


/-- Little-endian trailing-zero removal. The recursive child is stored once.
The terminal visit costs one and each input bit costs three visits. -/
def trimCounted : List Bool → List Bool × ℕ
  | [] => ([],1)
  | b::bs =>
      let child := trimCounted bs
      (if child.1 = [] ∧ b = false then [] else b::child.1,child.2+3)

theorem bits_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := value_bits n
    rw [h] at hv
    simpa only [value] using hv.symm
  · rintro rfl
    exact Nat.zero_bits

theorem trimCounted_canonical (bs : List Bool) :
    (trimCounted bs).1 = (value bs).bits := by
  induction bs with
  | nil => simp [trimCounted,value]
  | cons b bs ih =>
    cases b with
    | false =>
      by_cases hz : value bs = 0
      · simp [trimCounted,ih,hz,value]
      · have hb : (value bs).bits ≠ [] := by
          intro he
          exact hz ((bits_nil_iff _).mp he)
        simp [trimCounted,ih,hb,value,Nat.bit0_bits _ hz]
    | true =>
      simp only [trimCounted,ih,value,digit_true]
      simp only [Bool.true_eq_false,and_false,if_false]
      rw [Nat.add_comm 1 (2*value bs),Nat.bit1_bits]

@[simp] theorem trimCounted_value (bs : List Bool) :
    value (trimCounted bs).1 = value bs := by
  rw [trimCounted_canonical,value_bits]

@[simp] theorem trimCounted_length (bs : List Bool) :
    (trimCounted bs).1.length = (value bs).size := by
  rw [trimCounted_canonical,Nat.size_eq_bits_len]

@[simp] theorem trimCounted_work (bs : List Bool) :
    (trimCounted bs).2 = 3*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [trimCounted,ih,List.length_cons]; omega

theorem trimCounted_length_le (bs : List Bool) :
    (trimCounted bs).1.length ≤ bs.length := by
  rw [trimCounted_length]
  exact value_size bs

/-- Copies the sign and normalizes only the stored magnitude. Negative zero
is permitted by SignedBits, so no value inspection or Int conversion occurs. -/
def normalizeCounted (x : SignedBits) : SignedBits × ℕ :=
  let child := trimCounted x.magnitude
  (⟨x.negative,child.1⟩,child.2+1)

@[simp] theorem normalizeCounted_correct (x : SignedBits) :
    signedValue (normalizeCounted x).1 = signedValue x := by
  simp only [normalizeCounted,signedValue,trimCounted_value]

@[simp] theorem normalizeCounted_length (x : SignedBits) :
    (normalizeCounted x).1.magnitude.length = (signedValue x).natAbs.size := by
  simp only [normalizeCounted,trimCounted_length,signedValue_natAbs]

@[simp] theorem normalizeCounted_work (x : SignedBits) :
    (normalizeCounted x).2 = 3*x.magnitude.length+2 := by
  simp only [normalizeCounted,trimCounted_work]

theorem normalizeCounted_length_le (x : SignedBits) :
    (normalizeCounted x).1.magnitude.length ≤ x.magnitude.length := by
  rw [normalizeCounted_length]
  exact signedValue_size x


inductive ScalarInstruction where
  | add (x y : SignedBits)
  | subtract (x y : SignedBits)
  | multiply (x y : SignedBits)
  | divide (divisor : List Bool) (x : SignedBits)
  | copy (x : SignedBits)

def ScalarInstruction.Fits (B : ℕ) : ScalarInstruction → Prop
  | .add x y | .subtract x y | .multiply x y => x.magnitude.length ≤ B ∧ y.magnitude.length ≤ B
  | .divide D x => x.magnitude.length ≤ B ∧ D.length ≤ B
  | .copy x => x.magnitude.length ≤ B

def rawExecute : ScalarInstruction → SignedBits × ℕ
  | .add x y => signedAddCounted x y
  | .subtract x y => subtractCounted x y
  | .multiply x y => signedMulCounted x y
  | .divide D x => signedDivideCounted D x
  | .copy x => copyCell x

def instructionValue : ScalarInstruction → ℤ
  | .add x y => signedValue x+signedValue y
  | .subtract x y => signedValue x-signedValue y
  | .multiply x y => signedValue x*signedValue y
  | .divide D x => signedValue (signedDivide D x)
  | .copy x => signedValue x

/-- The result remains in binary form. Canonicalization trims actual bits;
no opaque Int-to-bits conversion appears in the executable program. -/
def execute (op : ScalarInstruction) : SignedBits × ℕ :=
  let raw := rawExecute op
  let normalized := normalizeCounted raw.1
  (normalized.1,raw.2+normalized.2)

theorem rawExecute_price (B : ℕ) (op : ScalarInstruction) (h : op.Fits B) :
    (rawExecute op).2 ≤ scalarUnit B := by
  cases op with
  | add x y => exact add_price B x y h.1 h.2
  | subtract x y => exact subtract_price B x y h.1 h.2
  | multiply x y => exact multiply_price B x y h.1 h.2
  | divide D x => exact divide_price B D x h.1 h.2
  | copy x => exact copyCell_price B x h

theorem rawExecute_width (B : ℕ) (op : ScalarInstruction) (h : op.Fits B) :
    (rawExecute op).1.magnitude.length ≤ 3*B+1 := by
  cases op with
  | add x y =>
      rw [rawExecute,(signedAddCounted_projections x y).1]
      exact (signedAdd_length x y).trans (by have hm:=max_le h.1 h.2; omega)
  | subtract x y =>
      simp only [rawExecute,subtractCounted,(signedAddCounted_projections _ _).1]
      exact (signedAdd_length x (signedNeg y)).trans (by
        have hm:=max_le h.1 h.2
        simpa only [signedNeg] using (show max x.magnitude.length y.magnitude.length+1≤3*B+1 by omega))
  | multiply x y => exact multiply_output_width B x y h.1 h.2
  | divide D x =>
      simp only [rawExecute,(signedDivideCounted_projections _ _).1,signedDivide,divideBits_quotient_length]
      exact h.1.trans (by omega)
  | copy x => simpa only [rawExecute,copyCell_value] using h.trans (by omega)

theorem execute_correct (op : ScalarInstruction) : signedValue (execute op).1 = instructionValue op := by
  simp only [execute,normalizeCounted_correct]
  cases op with
  | add x y => exact (congrArg signedValue (signedAddCounted_projections x y).1).trans (signedAdd_correct x y)
  | subtract x y => exact subtract_correct x y
  | multiply x y => exact (congrArg signedValue (signedMulCounted_projections x y).1).trans (signedMul_correct x y)
  | divide D x => exact congrArg signedValue (signedDivideCounted_projections D x).1
  | copy x => simp [rawExecute,instructionValue]

theorem execute_canonical_width (op : ScalarInstruction) :
    (execute op).1.magnitude.length = (instructionValue op).natAbs.size := by
  simp only [execute,normalizeCounted_length]
  have h : signedValue (rawExecute op).1 = instructionValue op := by
    simpa only [execute,normalizeCounted_correct] using execute_correct op
  rw [h]

theorem execute_price (B : ℕ) (op : ScalarInstruction) (h : op.Fits B) :
    (execute op).2 ≤ 2*scalarUnit B := by
  have hr := rawExecute_price B op h
  have hw := rawExecute_width B op h
  have hn : (normalizeCounted (rawExecute op).1).2 ≤ scalarUnit B := by
    rw [normalizeCounted_work]
    unfold scalarUnit
    nlinarith
  exact (Nat.add_le_add hr hn).trans_eq (by ring)

/-- Indexed cell interface: the address and coefficient payload are copied
bitwise, and one RAM cell access is charged. Array-to-RAM simulation is separate. -/
def transferCell (address : List Bool) (x : SignedBits) : SignedBits × ℕ :=
  let a := copyBits address
  let data := copyCell x
  (data.1,a.2+data.2+1)

theorem transferCell_correct (address : List Bool) (x : SignedBits) : (transferCell address x).1 = x := by
  simp [transferCell]

theorem transferCell_price (B : ℕ) (address : List Bool) (x : SignedBits)
    (ha : address.length ≤ B) (hx : x.magnitude.length ≤ B) :
    (transferCell address x).2 ≤ scalarUnit B := by
  simp only [transferCell,copyBits_work,copyCell,copyBits_work]
  unfold scalarUnit
  nlinarith

/-- Enough for a normalized arithmetic primitive, operand/output transfer,
and a bounded scalar control action under one common width. -/
def backendScalarUnit (B : ℕ) : ℕ := 8*scalarUnit B

def executeAll : List ScalarInstruction → List SignedBits × ℕ
  | [] => ([],0)
  | op::ops =>
      let head := execute op
      let tail := executeAll ops
      (head.1::tail.1,head.2+tail.2)

theorem executeAll_correct (ops : List ScalarInstruction) :
    (executeAll ops).1.map signedValue = ops.map instructionValue := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [executeAll,List.map_cons,execute_correct,ih]

theorem executeAll_price (B : ℕ) (ops : List ScalarInstruction)
    (h : ∀ op ∈ ops, op.Fits B) :
    (executeAll ops).2 ≤ ops.length*backendScalarUnit B := by
  induction ops with
  | nil => simp [executeAll]
  | cons op ops ih =>
      have hh := execute_price B op (h op (by simp))
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [executeAll,List.length_cons]
      unfold backendScalarUnit at ht ⊢
      nlinarith

private theorem normal_source_schema {q : ℕ} [NeZero q] (row : Fin 6) (col : Fin 4) :
    CachedLowIdentity.normalCacheForm (SourceCoordinates.normalEquiv col) row =
      PipelineBitBounds.localPolynomial (q := q) true row col := by
  change CachedLowIdentity.normalCacheForm (![.x1,.x2,.p1,.p2] col) row = _
  fin_cases row <;> fin_cases col <;>
    simp [CachedLowIdentity.normalCacheForm,PipelineBitBounds.localPolynomial,
      CoefficientBounds.normalRowCoefficients,CompleteThinProduct.normalForm,
      TensorContraction.alignedLeft,CompleteThinProduct.letterIndicator]

private theorem opposite_source_schema {q : ℕ} [NeZero q] (row : Fin 6) (col : Fin 4) :
    (if h : col.val < 3 then
      CachedLowIdentity.oppositeCacheForm (SourceCoordinates.oppositeEquiv ⟨col.val,h⟩) row else 0) =
      PipelineBitBounds.localPolynomial (q := q) false row col := by
  change (if h : col.val < 3 then
    CachedLowIdentity.oppositeCacheForm (![.s,.v,.w] ⟨col.val,h⟩) row else 0) = _
  fin_cases row <;> fin_cases col <;>
    simp [CachedLowIdentity.oppositeCacheForm,PipelineBitBounds.localPolynomial,
      CoefficientBounds.oppositeRowCoefficients,CompleteThinProduct.oppositeForm,
      TensorContraction.alignedRight,CompleteThinProduct.letterIndicator,
      Polynomial.C_ofNat]

/-- The actual lowered source rows are exactly the schema used by the
stored-array magnitude proofs, including the zero fourth opposite column. -/
theorem sourceCacheForms_eq_cacheForms {q : ℕ} [NeZero q] (L : ℕ) (side : Bool) :
    CachedLowIdentity.sourceCacheForms (R := CyclicRing.Cyclic q) L side =
      PipelineBitBounds.cacheForms (CacheDenseLowering.normalHere L side) := by
  funext d row raw
  by_cases hn : (d < L) = (side = true)
  · simp only [CachedLowIdentity.sourceCacheForms,hn,ite_true,PipelineBitBounds.cacheForms,
      CacheDenseLowering.normalHere,decide_true]
    split
    · exact normal_source_schema row _
    · rfl
  · simp only [CachedLowIdentity.sourceCacheForms,hn,ite_false,PipelineBitBounds.cacheForms,
      CacheDenseLowering.normalHere,decide_false]
    by_cases hr : raw < 4
    · rw [dif_pos hr]
      exact opposite_source_schema row ⟨raw,hr⟩
    · have ht : ¬raw < 3 := by omega
      simp only [dif_neg ht,dif_neg hr]

/-- The existing factorial constructor's three factorials and denominator
product all fit this actual quadratic-width setup budget. -/
theorem weight_setup_widths (k t degree : ℕ) :
    let B := CachedLowQuery.weightBitWidth k t
    (CachedLowQuery.factorialCounted (k-degree-1)).1.size ≤ B ∧
    (CachedLowQuery.factorialCounted (t-degree-1)).1.size ≤ B ∧
    (CachedLowQuery.factorialCounted (k-degree-1-(t-degree-1))).1.size ≤ B ∧
    ((CachedLowQuery.factorialCounted (t-degree-1)).1*
      (CachedLowQuery.factorialCounted (k-degree-1-(t-degree-1))).1).size ≤ B := by
  dsimp only
  have h := CachedLowQuery.weight_factorial_temporaries k t degree
  dsimp only at h
  have ha := (Nat.size_le_size h.1).trans_eq Nat.size_pow
  have hb := (Nat.size_le_size h.2.1).trans_eq Nat.size_pow
  have hc := (Nat.size_le_size h.2.2.1).trans_eq Nat.size_pow
  have hd := (Nat.size_le_size h.2.2.2).trans_eq Nat.size_pow
  unfold CachedLowQuery.weightBitWidth
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- Common width includes data, factorial setup, normalization denominator,
and binary addresses. The four terms correspond to separate proved bounds. -/
def backendWidth (dataBits L m t addressBits : ℕ) : ℕ :=
  dataBits+CachedLowQuery.weightBitWidth (2*m) t+2*L+addressBits+4

theorem backendWidth_data (dataBits L m t addressBits : ℕ) :
    dataBits ≤ backendWidth dataBits L m t addressBits := by unfold backendWidth; omega

theorem backendWidth_weights (dataBits L m t addressBits : ℕ) :
    CachedLowQuery.weightBitWidth (2*m) t ≤ backendWidth dataBits L m t addressBits := by
  unfold backendWidth
  omega

theorem backendWidth_denominator (dataBits L m t addressBits : ℕ) :
    (4^L).size ≤ backendWidth dataBits L m t addressBits := by
  have h : (4^L).size = 2*L+1 := by
    rw [show (4:ℕ)=2^2 by norm_num,←pow_mul,Nat.size_pow]
  rw [h]
  unfold backendWidth
  omega

/-- Explicit quartic-logarithmic scalar price when the source, rounded
length, inner exponent, and addresses have the established linear bounds. -/
def widthConstant (dataC cL cm addressC : ℕ) : ℕ :=
  dataC+2*(4*cm+2)^2+2*cL+addressC+10

theorem backendWidth_le_quadratic (r dataBits L m t addressBits dataC cL cm addressC : ℕ)
    (hd : dataBits ≤ dataC*(r+1)) (hL : L ≤ cL*r) (hm : m ≤ cm*r)
    (ht : t ≤ 2*m) (ha : addressBits ≤ addressC*(r+1)) :
    backendWidth dataBits L m t addressBits ≤ widthConstant dataC cL cm addressC*(r+1)^2 := by
  have hs : 2*m+t+2 ≤ (4*cm+2)*(r+1) := by nlinarith
  have hsq : (2*m+t+2)^2 ≤ (4*cm+2)^2*(r+1)^2 := by nlinarith
  have hr : r+1 ≤ (r+1)^2 := by nlinarith
  have hd' : dataBits ≤ dataC*(r+1)^2 := hd.trans (Nat.mul_le_mul_left _ hr)
  have ha' : addressBits ≤ addressC*(r+1)^2 := ha.trans (Nat.mul_le_mul_left _ hr)
  have hl' : 2*L ≤ 2*cL*(r+1)^2 := by nlinarith
  have hone : 1 ≤ (r+1)^2 := by nlinarith
  unfold backendWidth CachedLowQuery.weightBitWidth widthConstant
  nlinarith

theorem scalarUnit_le_quartic (r B C : ℕ) (hB : B ≤ C*(r+1)^2) :
    scalarUnit B ≤ 100*(C+1)^2*(r+1)^4 := by
  have hp : 1 ≤ (r+1)^2 := Nat.one_le_pow 2 (r+1) (by omega)
  have h : B+1 ≤ (C+1)*(r+1)^2 := by nlinarith
  unfold scalarUnit
  nlinarith


/-- The omitted inner LOW dot-product prefix is bounded even before its
channel weight is applied. Arbitrary partial supports allow every loop order. -/
theorem innerDot_partial_bound {q width d : ℕ} [NeZero q] (A : ℕ)
    (left right : SparseLocalForms.DenseVector q width)
    (hl : ∀ degree residue, |SparseLocalForms.denseRead left degree residue| ≤ (A:ℤ))
    (hr : ∀ degree residue, |SparseLocalForms.denseRead right degree residue| ≤ (A:ℤ))
    (target : Fin q) (support : Finset (Fin (d+1) × Fin q)) :
    |∑ key ∈ support, CachedLowQuery.blockCoeff left key.1.val key.2 *
      CachedLowQuery.blockCoeff right (d-key.1.val) (target-key.2)| ≤ ((d+1)*q*A^2 : ℕ) := by
  have hb (block : SparseLocalForms.DenseVector q width)
      (h : ∀ degree residue, |SparseLocalForms.denseRead block degree residue| ≤ (A:ℤ))
      (degree : ℕ) (residue : Fin q) : |CachedLowQuery.blockCoeff block degree residue| ≤ (A:ℤ) := by
    unfold CachedLowQuery.blockCoeff
    split
    · exact h _ _
    · simp
  calc
    _ ≤ ∑ key ∈ support, |CachedLowQuery.blockCoeff left key.1.val key.2 *
        CachedLowQuery.blockCoeff right (d-key.1.val) (target-key.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _key ∈ support, ((A:ℤ)*(A:ℤ)) := by
      apply Finset.sum_le_sum
      intro key _
      rw [abs_mul]
      exact mul_le_mul (hb left hl _ _) (hb right hr _ _) (abs_nonneg _) (Nat.cast_nonneg A)
    _ = (support.card*A^2 : ℕ) := by simp [pow_two]
    _ ≤ _ := by
      have hc : support.card ≤ (d+1)*q := by simpa using support.card_le_univ
      exact_mod_cast Nat.mul_le_mul_right (A^2) hc

/-- The common scalar adapter remains polynomial in logarithmic input
size even with quadratic factorial and address widths. -/
theorem backendScalarUnit_le_quartic (r B C : ℕ) (hB : B ≤ C*(r+1)^2) :
    backendScalarUnit B ≤ 800*(C+1)^2*(r+1)^4 := by
  have h := Nat.mul_le_mul_left 8 (scalarUnit_le_quartic r B C hB)
  unfold backendScalarUnit
  exact h.trans_eq (by ring)


/-- Explicit construction of a binary power of two, used by source weights
and by the final 4^L denominator. Formation is linear in its stored width. -/
def powerTwoBits (k : ℕ) : List Bool × ℕ :=
  (List.replicate k false ++ [true],2*k+2)

theorem powerTwoBits_value (k : ℕ) : value (powerTwoBits k).1 = 2^k := by
  induction k with
  | zero => simp [powerTwoBits,value]
  | succ k ih =>
      simp only [powerTwoBits,List.replicate_succ,List.cons_append,value,digit_false,zero_add,pow_succ]
      change 2*value (powerTwoBits k).1 = _
      rw [ih]
      ring

@[simp] theorem powerTwoBits_length (k : ℕ) : (powerTwoBits k).1.length = k+1 := by
  simp [powerTwoBits]

theorem powerTwoBits_price (B k : ℕ) (hk : k+1 ≤ B) :
    (powerTwoBits k).2 ≤ scalarUnit B := by
  unfold powerTwoBits scalarUnit
  nlinarith

/-- The exact factorial quotient in chooseCounted is realized by actual
unsigned long division. The positivity and exact value are proved, rather
than assigning a unit cost to native Nat.div. -/
theorem choose_division_binary (n h : ℕ) (hh : h ≤ n) :
    value ((divideCounted (h.factorial*(n-h).factorial).bits n.factorial.bits).1.1) = n.choose h := by
  rw [(divideCounted_projections _ _).1,divideBits_quotient]
  · rw [value_bits,value_bits]
    exact (Nat.choose_eq_factorial_div_factorial hh).symm
  · rw [value_bits]
    exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

theorem choose_division_price (B n h : ℕ)
    (hn : n.factorial.size ≤ B) (hD : (h.factorial*(n-h).factorial).size ≤ B) :
    (divideCounted (h.factorial*(n-h).factorial).bits n.factorial.bits).2 ≤ scalarUnit B := by
  exact unsigned_divide_price B _ _ (by simpa only [Nat.size_eq_bits_len] using hn)
    (by simpa only [Nat.size_eq_bits_len] using hD)


/-- Comparisons used by natural indices and loop guards scan actual bits. -/
def unsignedLessCounted (x y : List Bool) : Bool × ℕ :=
  let difference := subCounted x y false
  (difference.1.2,difference.2)

theorem unsignedLess_correct (x y : List Bool) :
    (unsignedLessCounted x y).1 = true ↔ value x < value y := by
  simp only [unsignedLessCounted,(subCounted_projections _ _ _).1]
  exact subBits_borrow x y

theorem unsignedLess_price (B : ℕ) (x y : List Bool)
    (hx : x.length ≤ B) (hy : y.length ≤ B) :
    (unsignedLessCounted x y).2 ≤ scalarUnit B := by
  simp only [unsignedLessCounted,(subCounted_projections _ _ _).2,columnSteps_eq]
  have hm := max_le hx hy
  unfold scalarUnit
  nlinarith

theorem unsigned_divide_correct (D x : List Bool) (hD : 0 < value D) :
    value ((divideCounted D x).1.1) = value x / value D ∧
    value ((divideCounted D x).1.2) = value x % value D := by
  rw [(divideCounted_projections D x).1]
  refine ⟨divideBits_quotient D x hD,?_⟩
  have h := divideBits_correct D x hD
  rw [h.1,Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt h.2]
  exact (Nat.mod_eq_of_lt h.2).symm

theorem execute_exact_divide (D : List Bool) (x : SignedBits) (w : ℤ)
    (hD : 0 < value D) (hx : signedValue x = (value D : ℤ)*w) :
    signedValue (execute (.divide D x)).1 = w := by
  rw [execute_correct]
  exact signedDivide_exact D x w hD hx

/- This executes only binary lists, including canonicalization. -/
#eval let x : SignedBits := ⟨false,[true,true,true]⟩
  let y : SignedBits := ⟨true,[false,true]⟩
  let result := execute (.multiply x y)
  (signedValue result.1,result.1.magnitude.length,result.2)

#print axioms unsignedLess_correct
#print axioms unsignedLess_price
#print axioms unsigned_divide_correct
#print axioms execute_exact_divide
#print axioms powerTwoBits_value
#print axioms choose_division_binary
#print axioms choose_division_price
#print axioms add_price
#print axioms multiply_price
#print axioms divide_price
#print axioms exact_divide_correct
#print axioms unsigned_divide_price
#print axioms normalizeCounted_correct
#print axioms execute_correct
#print axioms execute_canonical_width
#print axioms executeAll_price
#print axioms innerDot_partial_bound
#print axioms backendScalarUnit_le_quartic
#print axioms sourceCacheForms_eq_cacheForms
#print axioms weight_setup_widths
#print axioms backendWidth_le_quadratic
#print axioms scalarUnit_le_quartic

end ThinMatrix.BackendScalarBits
