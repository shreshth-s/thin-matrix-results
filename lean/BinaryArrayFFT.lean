import FFTBitCost

/-!
# Binary-register lowering of the stored FFT

Runtime integer cells contain signed Boolean lists with canonical-magnitude
proofs. Denotational integers are used only in types and correctness proofs.
All computed integer values pass through the charged binary register
operations. Boundary loading is reserved for public control constants and
the original input encoding. Arrays provide bounded indexed storage; their
primitive-action model remains separate from bit-circuit costs.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace ThinMatrix.BinaryArrayFFT

open IntegerArithmetic FFTBitCost
open scoped BigOperators

structure Integer where
  bits : SignedBits
  canonical : bits.magnitude.length = (signedValue bits).natAbs.size

structure Cell where
  re : SignedBits
  im : SignedBits
  reCanonical : re.magnitude.length = (signedValue re).natAbs.size
  imCanonical : im.magnitude.length = (signedValue im).natAbs.size

def Integer.view (a : Integer) : ℤ := signedValue a.bits
def Cell.view (a : Cell) : FixedPointComplex.Cell := ⟨signedValue a.re, signedValue a.im⟩

def Integer.register (a : Integer) : Register a.view := ⟨a.bits, rfl, a.canonical⟩
def Cell.reRegister (a : Cell) : Register a.view.re := ⟨a.re, rfl, a.reCanonical⟩
def Cell.imRegister (a : Cell) : Register a.view.im := ⟨a.im, rfl, a.imCanonical⟩

def integerOfRegister {z : ℤ} (a : Register z) : Integer :=
  ⟨a.bits, by rw [a.denotes]; exact a.canonical⟩

def cellOfRegisters {r i : ℤ} (a : Register r) (b : Register i) : Cell :=
  ⟨a.bits, b.bits, by rw [a.denotes]; exact a.canonical, by rw [b.denotes]; exact b.canonical⟩

@[simp] theorem integerOfRegister_view {z : ℤ} (a : Register z) : (integerOfRegister a).view = z := a.denotes
@[simp] theorem cellOfRegisters_view {r i : ℤ} (a : Register r) (b : Register i) :
    (cellOfRegisters a b).view = (⟨r, i⟩ : FixedPointComplex.Cell) := by
  apply FixedPointComplex.Cell.ext <;> simp [Cell.view, cellOfRegisters, a.denotes, b.denotes]

def zeroInteger : Integer := ⟨⟨false, []⟩, rfl⟩
def zeroCell : Cell := ⟨⟨false, []⟩, ⟨false, []⟩, rfl, rfl⟩

@[simp] theorem zeroInteger_view : zeroInteger.view = 0 := rfl
@[simp] theorem zeroCell_view : zeroCell.view = ApproximateConvolution.zero := rfl

/-- Only the original boundary input is encoded from a semantic integer. -/
def loadInteger (z : ℤ) : BinaryResult Integer :=
  let child := registerInput z
  ⟨integerOfRegister child.value, child.bitSteps⟩

@[simp] theorem loadInteger_view (z : ℤ) : (loadInteger z).value.view = z := by
  exact (registerInput z).value.denotes

/-- Public scale construction uses the existing binary power dataflow. -/
def scale (B : ℕ) : BinaryResult (Register ((2 ^ B : ℕ) : ℤ)) :=
  let two := registerInput 2
  let child := binaryRegisterPower two.value B
  ⟨child.value.cast (by push_cast; rfl), two.bitSteps + child.bitSteps⟩

def cellAdd (a b : Cell) : BinaryResult Cell :=
  let re := registerAdd a.reRegister b.reRegister
  let im := registerAdd a.imRegister b.imRegister
  ⟨cellOfRegisters re.value im.value, re.bitSteps + im.bitSteps⟩

@[simp] theorem cellAdd_view (a b : Cell) :
    (cellAdd a b).value.view = FixedPointComplex.add a.view b.view := by
  simp only [cellAdd, cellOfRegisters_view]
  rfl

def cellMul (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Cell) : BinaryResult Cell :=
  let rr := registerMul a.reRegister b.reRegister
  let ii := registerMul a.imRegister b.imRegister
  let realNumerator := registerSub rr.value ii.value
  let ri := registerMul a.reRegister b.imRegister
  let ir := registerMul a.imRegister b.reRegister
  let imagNumerator := registerAdd ri.value ir.value
  let re := registerFloor realNumerator.value s
  let im := registerFloor imagNumerator.value s
  ⟨cellOfRegisters re.value im.value,
    rr.bitSteps + ii.bitSteps + realNumerator.bitSteps + ri.bitSteps + ir.bitSteps + imagNumerator.bitSteps +
      re.bitSteps + im.bitSteps⟩

@[simp] theorem cellMul_view (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Cell) :
    (cellMul B s a b).value.view = FixedPointComplex.mul B a.view b.view := by
  simp only [cellMul, cellOfRegisters_view, FixedPointComplex.mul, FixedPointComplex.mulRe,
    FixedPointComplex.mulIm, FixedPointComplex.scaleZ, Nat.cast_pow, Nat.cast_ofNat]

def cellConjugate (a : Cell) : BinaryResult Cell :=
  let im := registerNeg a.imRegister
  ⟨cellOfRegisters a.reRegister im.value, im.bitSteps⟩

@[simp] theorem cellConjugate_view (a : Cell) :
    (cellConjugate a).value.view = ApproximateConvolution.conjugate a.view := by
  simp only [cellConjugate, cellOfRegisters_view]
  rfl

def twiddle (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (j : ℕ) : BinaryResult Cell :=
  let raw := binaryRoot (2 ^ k) j B
  let reScaled := registerMul raw.value.re s
  let imScaled := registerMul raw.value.im s
  let re := registerFloor reScaled.value raw.value.den
  let im := registerFloor imScaled.value raw.value.den
  let cell := cellOfRegisters re.value im.value
  if inverse then
    let output := cellConjugate cell
    ⟨output.value, raw.bitSteps + reScaled.bitSteps + imScaled.bitSteps + re.bitSteps + im.bitSteps + output.bitSteps⟩
  else ⟨cell, raw.bitSteps + reScaled.bitSteps + imScaled.bitSteps + re.bitSteps + im.bitSteps⟩

@[simp] theorem twiddle_view (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (j : ℕ) :
    (twiddle B k s inverse j).value.view = ApproximateConvolution.twiddle B k inverse j := by
  have hr := RationalWorkBounds.rootC_result (2 ^ k) j B
  cases inverse <;>
    simp only [twiddle, Bool.false_eq_true, if_false, if_true,
      cellConjugate_view, cellOfRegisters_view, ApproximateConvolution.twiddle,
      ApproximateConvolution.ofRaw, hr, FixedPointComplex.scaleZ, Nat.cast_pow, Nat.cast_ofNat]

def embed (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Integer) : BinaryResult Cell :=
  let re := registerMul a.register s
  let zero := registerInput 0
  ⟨cellOfRegisters re.value zero.value, re.bitSteps + zero.bitSteps⟩

@[simp] theorem embed_view (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Integer) :
    (embed B s a).value.view = ApproximateConvolution.embed B a.view := by
  simp only [embed, cellOfRegisters_view, ApproximateConvolution.embed, FixedPointComplex.scaleZ,
    Nat.cast_pow, Nat.cast_ofNat]

def normalize (N : ℕ) (d : Register (N : ℤ)) (a : Cell) : BinaryResult Cell :=
  let re := registerFloor a.reRegister d
  let im := registerFloor a.imRegister d
  ⟨cellOfRegisters re.value im.value, re.bitSteps + im.bitSteps⟩

@[simp] theorem normalize_view (N : ℕ) (d : Register (N : ℤ)) (a : Cell) :
    (normalize N d a).value.view = ApproximateConvolution.normalize N a.view := by
  simp only [normalize, cellOfRegisters_view]
  rfl

def recover (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Cell) : BinaryResult Integer :=
  let two := registerInput 2
  let twiceReal := registerMul two.value a.reRegister
  let numerator := registerAdd twiceReal.value s
  let denominator := registerMul two.value s
  let quotient := registerFloor numerator.value (denominator.value.cast (by push_cast; rfl))
  ⟨integerOfRegister quotient.value,
    two.bitSteps + twiceReal.bitSteps + numerator.bitSteps + denominator.bitSteps + quotient.bitSteps⟩

@[simp] theorem recover_view (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Cell) :
    (recover B s a).value.view = FixedPointComplex.recover B a.view := by
  simp only [recover, integerOfRegister_view, FixedPointComplex.recover, FixedPointComplex.scaleZ,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Every callback runs once; its value and bit counter are stored together. -/
def tabulate {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) : BinaryResult (Array α) :=
  let cells := Array.ofFn f
  ⟨cells.map (fun c => c.value), cells.foldl (fun cost c => cost + c.bitSteps) 0⟩

theorem tabulate_value {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).value = Array.ofFn (fun i => (f i).value) := by
  simp [tabulate, Function.comp_def]

theorem tabulate_getD {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) (i : ℕ) (hi : i < N) (d : α) :
    (tabulate N f).value.getD i d = (f ⟨i, hi⟩).value := by
  rw [tabulate_value, ArrayFFT.getD_ofFn _ i hi]

theorem array_fold_cost_eq {α : Type} (a : Array α) (cost : α → ℕ) :
    a.foldl (fun total x => total+cost x) 0 = (a.toList.map cost).sum := by
  rw [← Array.foldl_toList]
  rw [← List.foldl_map]
  exact (List.sum_eq_foldl).symm

theorem list_sum_cost_bound {α : Type} (l : List α) (cost : α → ℕ) (C : ℕ)
    (hC : ∀ x ∈ l, cost x ≤ C) : (l.map cost).sum ≤ l.length*C := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hC a (by simp)
      have hl := ih (fun x hx => hC x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith


/-- Finite-sum specification of array accumulation, used only in proofs. -/
theorem array_ofFn_fold_cost {α : Type} {N : ℕ}
    (f : Fin N → α) (cost : α → ℕ) :
    (Array.ofFn f).foldl (fun total x => total+cost x) 0 =
      ∑ i : Fin N, cost (f i) := by
  rw [← Array.foldl_toList, Array.toList_ofFn, ← List.foldl_map,
    ← List.sum_eq_foldl, List.map_ofFn, List.sum_ofFn]
  rfl

theorem tabulate_bitSteps_eq {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).bitSteps = ∑ i : Fin N, (f i).bitSteps :=
  array_ofFn_fold_cost f BinaryResult.bitSteps

/-- Bound for a genuine Array.foldl over stored results. -/
theorem array_fold_cost_bound {α : Type} (a : Array α) (cost : α → ℕ) (C : ℕ)
    (hC : ∀ x ∈ a, cost x ≤ C) :
    a.foldl (fun total x => total+cost x) 0 ≤ a.size*C := by
  rw [array_fold_cost_eq]
  have h := list_sum_cost_bound a.toList cost C (by simpa using hC)
  simpa using h

theorem tabulate_bitSteps_bound {α : Type} (N : ℕ)
    (f : Fin N → BinaryResult α) (C : ℕ) (hC : ∀ i, (f i).bitSteps ≤ C) :
    (tabulate N f).bitSteps ≤ N*C := by
  change (Array.ofFn f).foldl (fun total result => total+result.bitSteps) 0 ≤ N*C
  have h := array_fold_cost_bound (Array.ofFn f) BinaryResult.bitSteps C (by
    intro x hx
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
    exact hC i)
  simpa using h



def viewCells (a : Array Cell) : Array FixedPointComplex.Cell := a.map Cell.view
def viewIntegers (a : Array Integer) : Array ℤ := a.map Integer.view

@[simp] theorem viewCells_getD (a : Array Cell) (i : ℕ) :
    (viewCells a).getD i ApproximateConvolution.zero = (a.getD i zeroCell).view := by
  by_cases hi : i < a.size <;> simp [viewCells, Array.getD, hi]

@[simp] theorem viewIntegers_getD (a : Array Integer) (i : ℕ) :
    (viewIntegers a).getD i 0 = (a.getD i zeroInteger).view := by
  by_cases hi : i < a.size <;> simp [viewIntegers, Array.getD, hi]

structure Result (α : Type) where
  value : Array α
  bitSteps : ℕ
  arrayActions : ℕ

def fft (B : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) : ℕ → Array Cell → Result Cell
  | 0, a => ⟨#[a.getD 0 zeroCell], 0, 8⟩
  | k + 1, a =>
      let half := 2 ^ k
      let full := 2 ^ (k + 1)
      let evenInput := Array.ofFn (fun i : Fin half => a.getD (2 * i.val) zeroCell)
      let oddInput := Array.ofFn (fun i : Fin half => a.getD (2 * i.val + 1) zeroCell)
      let even := fft B s inverse k evenInput
      let odd := fft B s inverse k oddInput
      let roots := tabulate full (fun j => twiddle B (k + 1) s inverse j.val)
      let output := tabulate full (fun j =>
        let index := j.val % half
        let product := cellMul B s (roots.value.getD j.val zeroCell) (odd.value.getD index zeroCell)
        let sum := cellAdd (even.value.getD index zeroCell) product.value
        ⟨sum.value, product.bitSteps + sum.bitSteps⟩)
      ⟨output.value, even.bitSteps + odd.bitSteps + roots.bitSteps + output.bitSteps,
        even.arrayActions + odd.arrayActions + 128 * full + 4 * k + 16⟩

theorem fft_size (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (a : Array Cell) :
    (fft B s inverse k a).value.size = 2 ^ k := by
  cases k <;> simp [fft, tabulate_value]


@[simp] theorem viewCells_ofFn {N : ℕ} (f : Fin N → Cell) :
    viewCells (Array.ofFn f) = Array.ofFn (fun i => (f i).view) := by
  simp [viewCells, Function.comp_def]

@[simp] theorem viewIntegers_ofFn {N : ℕ} (f : Fin N → Integer) :
    viewIntegers (Array.ofFn f) = Array.ofFn (fun i => (f i).view) := by
  simp [viewIntegers, Function.comp_def]

theorem fft_getD_succ (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (a : Array Cell)
    (j : ℕ) (hj : j < 2 ^ (k + 1)) :
    (fft B s inverse (k + 1) a).value.getD j zeroCell =
      (cellAdd
        ((fft B s inverse k (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val) zeroCell))).value.getD (j % 2 ^ k) zeroCell)
        (cellMul B s (twiddle B (k + 1) s inverse j).value
          ((fft B s inverse k (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val + 1) zeroCell))).value.getD (j % 2 ^ k) zeroCell)).value).value := by
  simp only [fft]
  rw [tabulate_getD _ _ j hj, tabulate_getD _ _ j hj]

theorem fft_view (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (a : Array Cell) :
    viewCells (fft B s inverse k a).value = (ArrayFFT.fft B inverse k (viewCells a)).value := by
  induction k generalizing a with
  | zero =>
      by_cases hi : 0 < a.size <;> simp [fft, ArrayFFT.fft, viewCells, Array.getD, hi]
  | succ k ih =>
      have he := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val) zeroCell))
      have ho := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val + 1) zeroCell))
      simp only [viewCells_ofFn, ← viewCells_getD] at he ho
      apply Array.ext
      · simp [viewCells, fft_size, ArrayFFT.fft_size]
      · intro j hj₁ hj₂
        have hj : j < 2 ^ (k + 1) := by simpa [viewCells, fft_size] using hj₁
        rw [Array.getElem_eq_getD ApproximateConvolution.zero,
          Array.getElem_eq_getD ApproximateConvolution.zero, viewCells_getD,
          fft_getD_succ B k s inverse a j hj, cellAdd_view, cellMul_view, twiddle_view,
          ArrayFFT.fft_getD_succ B k inverse (viewCells a) j hj]
        rw [← viewCells_getD, he, ← viewCells_getD, ho]



def embedArray (B N : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Array Integer) : BinaryResult (Array Cell) :=
  tabulate N (fun i => embed B s (a.getD i.val zeroInteger))

def pointwiseArray (B N : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Cell) : BinaryResult (Array Cell) :=
  tabulate N (fun i => cellMul B s (a.getD i.val zeroCell) (b.getD i.val zeroCell))

def normalizeArray (N : ℕ) (d : Register (N : ℤ)) (a : Array Cell) : BinaryResult (Array Cell) :=
  tabulate N (fun i => normalize N d (a.getD i.val zeroCell))

theorem embedArray_view (B N : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a : Array Integer) :
    viewCells (embedArray B N s a).value = ArrayFFT.embedArray B N (viewIntegers a) := by
  simp only [embedArray, tabulate_value, viewCells_ofFn, embed_view, ArrayFFT.embedArray, viewIntegers_getD]

theorem pointwiseArray_view (B N : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Cell) :
    viewCells (pointwiseArray B N s a b).value = ArrayFFT.pointwiseArray B N (viewCells a) (viewCells b) := by
  simp only [pointwiseArray, tabulate_value, viewCells_ofFn, cellMul_view,
    ArrayFFT.pointwiseArray, viewCells_getD]

theorem normalizeArray_view (N : ℕ) (d : Register (N : ℤ)) (a : Array Cell) :
    viewCells (normalizeArray N d a).value = ArrayFFT.normalizeArray N (viewCells a) := by
  simp only [normalizeArray, tabulate_value, viewCells_ofFn, normalize_view,
    ArrayFFT.normalizeArray, viewCells_getD]

def convolutionCore (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Integer) : Result Cell :=
  let N : ℕ := 2 ^ k
  let denominator := registerInput (N : ℤ)
  let leftInput := embedArray B N s a
  let rightInput := embedArray B N s b
  let left := fft B s false k leftInput.value
  let right := fft B s false k rightInput.value
  let frequencies := pointwiseArray B N s left.value right.value
  let inverse := fft B s true k frequencies.value
  let output := normalizeArray N denominator.value inverse.value
  ⟨output.value, denominator.bitSteps + leftInput.bitSteps + rightInput.bitSteps +
    left.bitSteps + right.bitSteps + frequencies.bitSteps + inverse.bitSteps + output.bitSteps,
    left.arrayActions + right.arrayActions + inverse.arrayActions + 512 * N + 4 * k + 32⟩

def convolution (B k : ℕ) (a b : Array Integer) : Result Cell :=
  let scaling := scale B
  let output := convolutionCore B k scaling.value a b
  ⟨output.value, scaling.bitSteps + output.bitSteps, output.arrayActions + 8⟩

theorem convolutionCore_view (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Integer) :
    viewCells (convolutionCore B k s a b).value = (ArrayFFT.convolution B k (viewIntegers a) (viewIntegers b)).value := by
  simp only [convolutionCore, normalizeArray_view, fft_view, pointwiseArray_view, embedArray_view, ArrayFFT.convolution]

theorem convolution_view (B k : ℕ) (a b : Array Integer) :
    viewCells (convolution B k a b).value = (ArrayFFT.convolution B k (viewIntegers a) (viewIntegers b)).value :=
  convolutionCore_view B k _ a b

def pad (q N : ℕ) (a : Array Integer) : Array Integer :=
  Array.ofFn (fun i : Fin N => if i.val < q then a.getD i.val zeroInteger else zeroInteger)

theorem pad_view (q N : ℕ) (a : Array Integer) : viewIntegers (pad q N a) = ArrayFFT.pad q N (viewIntegers a) := by
  simp only [pad, viewIntegers_ofFn, ArrayFFT.pad, viewIntegers_getD]
  congr 1
  funext i
  split <;> simp_all

def cyclic (q B k : ℕ) (a b : Array Integer) : Result Integer :=
  let N : ℕ := 2 ^ k
  let scaling := scale B
  let product := convolutionCore B k scaling.value (pad q N a) (pad q N b)
  let output := tabulate q (fun j =>
    let folded := cellAdd (product.value.getD j.val zeroCell) (product.value.getD (j.val + q) zeroCell)
    let recovered := recover B scaling.value folded.value
    ⟨recovered.value, folded.bitSteps + recovered.bitSteps⟩)
  ⟨output.value, scaling.bitSteps + product.bitSteps + output.bitSteps,
    product.arrayActions + 128 * N + 64 * q + 4 * k + 32⟩

theorem cyclic_view (q B k : ℕ) (a b : Array Integer) :
    viewIntegers (cyclic q B k a b).value = (ArrayFFT.cyclic q B k (viewIntegers a) (viewIntegers b)).value := by
  simp only [cyclic, tabulate_value, viewIntegers_ofFn, recover_view, cellAdd_view,
    ← viewCells_getD, convolutionCore_view, pad_view, ArrayFFT.cyclic]

def multiplication (q A : ℕ) (a b : Array Integer) : Result Integer :=
  let k := FastConvolution.paddedExponent q
  let B := ApproximateConvolution.convPrecision k A
  let output := cyclic q B k a b
  ⟨output.value, output.bitSteps, output.arrayActions + 64 * (k + A.log2 + 100) ^ 2⟩

theorem multiplication_view (q A : ℕ) (a b : Array Integer) :
    viewIntegers (multiplication q A a b).value = (ArrayFFT.multiplication q A (viewIntegers a) (viewIntegers b)).value :=
  cyclic_view q (ApproximateConvolution.convPrecision (FastConvolution.paddedExponent q) A)
    (FastConvolution.paddedExponent q) a b

theorem multiplication_getD_view (q A : ℕ) (a b : Array Integer) (j : ℕ) :
    ((multiplication q A a b).value.getD j zeroInteger).view =
      (ArrayFFT.multiplication q A (viewIntegers a) (viewIntegers b)).value.getD j 0 := by
  rw [← viewIntegers_getD, multiplication_view]

theorem multiplication_correct (q A : ℕ) [NeZero q] (hA : 1 ≤ A) (a b : Array Integer)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) (j : Fin q) :
    ((multiplication q A a b).value.getD j.val zeroInteger).view =
      CyclicRing.convolution (ArrayFFT.asCyclic q (viewIntegers a)) (ArrayFFT.asCyclic q (viewIntegers b)) j := by
  rw [multiplication_getD_view]
  apply ArrayFFT.multiplication_correct_natAbs q A hA _ _ _ _ j
  · intro i
    simpa only [viewIntegers_getD] using ha i
  · intro i
    simpa only [viewIntegers_getD] using hb i



theorem fft_arrayActions (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (inverse : Bool) (a : Array Cell) :
    (fft B s inverse k a).arrayActions ≤ 160 * (k + 1) * 2 ^ k := by
  induction k generalizing a with
  | zero => simp [fft]
  | succ k ih =>
      have he := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val) zeroCell))
      have ho := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val + 1) zeroCell))
      have hk := ArrayFFT.depth_le_length k
      simp only [fft]
      rw [pow_succ]
      nlinarith

theorem convolutionCore_arrayActions (B k : ℕ) (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Integer) :
    (convolutionCore B k s a b).arrayActions ≤ 1280 * (k + 1) * 2 ^ k := by
  have hl := fft_arrayActions B k s false (embedArray B (2 ^ k) s a).value
  have hr := fft_arrayActions B k s false (embedArray B (2 ^ k) s b).value
  have hi := fft_arrayActions B k s true (pointwiseArray B (2 ^ k) s
    (fft B s false k (embedArray B (2 ^ k) s a).value).value
    (fft B s false k (embedArray B (2 ^ k) s b).value).value).value
  have hk := ArrayFFT.depth_le_length k
  simp only [convolutionCore]
  nlinarith

theorem cyclic_arrayActions (q B k : ℕ) (a b : Array Integer) (hN : 2 * q ≤ 2 ^ k) :
    (cyclic q B k a b).arrayActions ≤ 1536 * (k + 1) * 2 ^ k := by
  have hc := convolutionCore_arrayActions B k (scale B).value (pad q (2 ^ k) a) (pad q (2 ^ k) b)
  have hk := ArrayFFT.depth_le_length k
  simp only [cyclic]
  nlinarith

theorem multiplication_arrayActions (q A : ℕ) [NeZero q] (a b : Array Integer) :
    let k := FastConvolution.paddedExponent q
    (multiplication q A a b).arrayActions ≤ 8192 * (k + 1) * q * (k + A.log2 + 100) ^ 2 := by
  let k := FastConvolution.paddedExponent q
  let S := k + A.log2 + 100
  have hN := FastConvolution.padded_length_bounds q (NeZero.pos q)
  have hc := cyclic_arrayActions q (ApproximateConvolution.convPrecision k A) k a b hN.1
  have hlen := Nat.mul_le_mul_left (1536 * (k + 1)) hN.2
  have hS : 1 ≤ S ^ 2 := one_le_pow₀ (show 1 ≤ S by dsimp [S]; omega)
  have hq : 1 ≤ q := NeZero.pos q
  have hM : 1 ≤ (k + 1) * q := by nlinarith
  have hm := Nat.mul_le_mul_left ((k + 1) * q) hS
  have hms := Nat.mul_le_mul_right (S ^ 2) hM
  change _ + 64 * S ^ 2 ≤ _
  dsimp only [k, S] at *
  nlinarith


#print axioms twiddle_view
#print axioms cellMul_view
#print axioms recover_view
#print axioms fft_view
#print axioms convolution_view
#print axioms cyclic_view
#print axioms multiplication_correct
#print axioms fft_arrayActions
#print axioms multiplication_arrayActions

end ThinMatrix.BinaryArrayFFT



namespace ThinMatrix.BinaryCellCost

open FFTBitCost
open RationalWorkBounds
namespace FP
abbrev Fits := FixedPointComplex.FitsMagnitudeBits
end FP

theorem fits_size {W : ℕ} {z : ℤ} (hz : FP.Fits W z) : z.natAbs.size ≤ W :=
  Nat.size_le.mpr hz

theorem magnitude_fits {R : ℕ} {z : ℤ} (hz : z.natAbs ≤ 2^R) : FP.Fits (R+1) z := by
  apply hz.trans_lt
  rw [pow_succ]
  have : 0 < (2:ℕ)^R := by positivity
  omega

theorem fits_mono {W V : ℕ} {z : ℤ} (hz : FP.Fits W z) (hWV : W ≤ V) :
    FP.Fits V z := hz.trans_le (Nat.pow_le_pow_right (by decide) hWV)

theorem product_fits {W : ℕ} {x y : ℤ} (hx : FP.Fits W x) (hy : FP.Fits W y) :
    FP.Fits (2 * W) (x*y) := by
  unfold FP.Fits FixedPointComplex.FitsMagnitudeBits at *
  rw [Int.natAbs_mul]
  calc
    x.natAbs * y.natAbs < 2^W * 2^W := Nat.mul_lt_mul_of_le_of_lt hx.le hy (by positivity)
    _ = 2^(2*W) := by rw [← pow_add]; congr 1; omega

theorem add_fits {W : ℕ} {x y : ℤ} (hx : FP.Fits W x) (hy : FP.Fits W y) :
    FP.Fits (W+1) (x+y) := by
  unfold FP.Fits FixedPointComplex.FitsMagnitudeBits at *
  calc
    (x+y).natAbs ≤ x.natAbs+y.natAbs := Int.natAbs_add_le _ _
    _ < 2^W+2^W := Nat.add_lt_add hx hy
    _ = 2^(W+1) := by rw [pow_succ]; omega

theorem sub_fits {W : ℕ} {x y : ℤ} (hx : FP.Fits W x) (hy : FP.Fits W y) :
    FP.Fits (W+1) (x-y) := by
  have hyn : FP.Fits W (-y) := by simpa [FP.Fits, FixedPointComplex.FitsMagnitudeBits] using hy
  simpa [sub_eq_add_neg] using add_fits hx hyn

theorem cell_mul_working_fits {W B : ℕ} {x y : FixedPointComplex.Cell}
    (hx : FixedPointComplex.CellFits W x) (hy : FixedPointComplex.CellFits W y) :
    FP.Fits (2*W) (x.re*y.re) ∧ FP.Fits (2*W) (x.im*y.im) ∧
    FP.Fits (2*W) (x.re*y.im) ∧ FP.Fits (2*W) (x.im*y.re) ∧
    FP.Fits (2*W+1) (FixedPointComplex.mulRe x y) ∧
    FP.Fits (2*W+1) (FixedPointComplex.mulIm x y) ∧
    FixedPointComplex.CellFits (2*W+1) (FixedPointComplex.mul B x y) := by
  have hrr := product_fits hx.1 hy.1
  have hii := product_fits hx.2 hy.2
  have hri := product_fits hx.1 hy.2
  have hir := product_fits hx.2 hy.1
  have hr : FP.Fits (2*W+1) (FixedPointComplex.mulRe x y) := sub_fits hrr hii
  have hi : FP.Fits (2*W+1) (FixedPointComplex.mulIm x y) := add_fits hri hir
  exact ⟨hrr,hii,hri,hir,hr,hi,
    (Int.natAbs_ediv_le_natAbs _ _).trans_lt hr,
    (Int.natAbs_ediv_le_natAbs _ _).trans_lt hi⟩

theorem register_add_cost {x y : ℤ} {W : ℕ} (a : Register x) (b : Register y)
    (hx : FP.Fits W x) (hy : FP.Fits W y) :
    (registerAdd a b).bitSteps ≤ 256*(W+2)^2 := by
  apply (registerAdd_price a b).trans
  change 256*(max x.natAbs.size y.natAbs.size+2)^2 ≤ _
  gcongr
  exact max_le (fits_size hx) (fits_size hy)

theorem register_sub_cost {x y : ℤ} {W : ℕ} (a : Register x) (b : Register y)
    (hx : FP.Fits W x) (hy : FP.Fits W y) :
    (registerSub a b).bitSteps ≤ 256*(W+2)^2 := by
  apply (registerSub_price a b).trans
  change 256*(max x.natAbs.size y.natAbs.size+2)^2 ≤ _
  gcongr
  exact max_le (fits_size hx) (fits_size hy)

theorem register_mul_cost {x y : ℤ} {W : ℕ} (a : Register x) (b : Register y)
    (hx : FP.Fits W x) (hy : FP.Fits W y) :
    (registerMul a b).bitSteps ≤ 256*(W+2)^2 := by
  apply (registerMul_price a b).trans
  change 256*(max x.natAbs.size y.natAbs.size+2)^2 ≤ _
  gcongr
  exact max_le (fits_size hx) (fits_size hy)

theorem register_floor_cost {x : ℤ} {d W : ℕ} (a : Register x) (b : Register (d:ℤ))
    (hx : FP.Fits W x) (hd : FP.Fits W (d:ℤ)) :
    (registerFloor a b).bitSteps ≤ 256*(W+2)^2 := by
  apply (registerFloor_price a b).trans
  change 256*(max d.size x.natAbs.size+2)^2 ≤ _
  gcongr
  have hd' := fits_size hd
  simpa using max_le hd' (fits_size hx)

theorem register_input_cost {z : ℤ} {W : ℕ} (hz : FP.Fits W z) :
    (registerInput z).bitSteps ≤ W+2 := by
  change z.natAbs.size+2 ≤ W+2
  have := fits_size hz
  omega

/-- The four coordinate products, two numerator additions/subtractions, and
two divisions of complex fixed-point multiplication, with their actual
binary-register counters. The inputs are already binary registers. -/
def cellMulCost {B : ℕ} {x y : FixedPointComplex.Cell}
    (xr : Register x.re) (xi : Register x.im) (yr : Register y.re) (yi : Register y.im)
    (scale : Register (FixedPointComplex.scaleZ B)) : ℕ :=
  let rr := registerMul xr yr
  let ii := registerMul xi yi
  let ri := registerMul xr yi
  let ir := registerMul xi yr
  let re := registerSub rr.value ii.value
  let im := registerAdd ri.value ir.value
  rr.bitSteps+ii.bitSteps+ri.bitSteps+ir.bitSteps+re.bitSteps+im.bitSteps+
    (registerFloor re.value scale).bitSteps+(registerFloor im.value scale).bitSteps

theorem cellMulCost_bound {B W : ℕ} {x y : FixedPointComplex.Cell}
    (xr : Register x.re) (xi : Register x.im) (yr : Register y.re) (yi : Register y.im)
    (scale : Register (FixedPointComplex.scaleZ B))
    (hx : FixedPointComplex.CellFits W x) (hy : FixedPointComplex.CellFits W y) :
    cellMulCost xr xi yr yi scale ≤ 2048*(max (2*W+1) (B+1)+2)^2 := by
  let V := max (2*W+1) (B+1)
  have hWV : W ≤ V := by dsimp [V]; omega
  have hPV : 2*W ≤ V := by dsimp [V]; omega
  have hNV : 2*W+1 ≤ V := le_max_left _ _
  have hSV : B+1 ≤ V := le_max_right _ _
  have hrr := register_mul_cost xr yr (fits_mono hx.1 hWV) (fits_mono hy.1 hWV)
  have hii := register_mul_cost xi yi (fits_mono hx.2 hWV) (fits_mono hy.2 hWV)
  have hri := register_mul_cost xr yi (fits_mono hx.1 hWV) (fits_mono hy.2 hWV)
  have hir := register_mul_cost xi yr (fits_mono hx.2 hWV) (fits_mono hy.1 hWV)
  have hp := cell_mul_working_fits (B := B) hx hy
  have hr := register_sub_cost (registerMul xr yr).value (registerMul xi yi).value
    (fits_mono hp.1 hPV) (fits_mono hp.2.1 hPV)
  have hi := register_add_cost (registerMul xr yi).value (registerMul xi yr).value
    (fits_mono hp.2.2.1 hPV) (fits_mono hp.2.2.2.1 hPV)
  have hs : FP.Fits V (FixedPointComplex.scaleZ B) :=
    fits_mono (FixedPointComplex.scale_bits B) hSV
  have hfr := register_floor_cost
    (registerSub (registerMul xr yr).value (registerMul xi yi).value).value scale
    (fits_mono hp.2.2.2.2.1 hNV) hs
  have hfi := register_floor_cost
    (registerAdd (registerMul xr yi).value (registerMul xi yr).value).value scale
    (fits_mono hp.2.2.2.2.2.1 hNV) hs
  change _ ≤ 2048*(V+2)^2
  dsimp only [cellMulCost]
  omega

/-- Conversion of an unreduced rational pair uses two actual binary
multiplications followed by two actual floor divisions. -/
def rawConversionCost {B : ℕ} {r : Raw} (a : RawRegisters r)
    (scale : Register (FixedPointComplex.scaleZ B)) : ℕ :=
  let reScaled := registerMul a.re scale
  let imScaled := registerMul a.im scale
  reScaled.bitSteps+imScaled.bitSteps+
    (registerFloor reScaled.value a.den).bitSteps+
    (registerFloor imScaled.value a.den).bitSteps

theorem rawConversionCost_bound {B R : ℕ} {r : Raw} (a : RawRegisters r)
    (scale : Register (FixedPointComplex.scaleZ B)) (hr : RationalWorkBounds.Fits r R) :
    rawConversionCost a scale ≤ 1024*(R+B+3)^2 := by
  let W := R+B+1
  have hR : R+1 ≤ W := by dsimp [W]; omega
  have hB : B+1 ≤ W := by dsimp [W]; omega
  have hre : FP.Fits W r.re := fits_mono (magnitude_fits hr.1) hR
  have him : FP.Fits W r.im := fits_mono (magnitude_fits hr.2.1) hR
  have hden : FP.Fits W (r.den:ℤ) :=
    fits_mono (magnitude_fits (by simpa using hr.2.2)) hR
  have hscale : FP.Fits W (FixedPointComplex.scaleZ B) :=
    fits_mono (FixedPointComplex.scale_bits B) hB
  have hpre := ApproximateConvolution.ofRaw_working_bits B R r hr
  have h₁ := register_mul_cost a.re scale hre hscale
  have h₂ := register_mul_cost a.im scale him hscale
  have h₃ := register_floor_cost (registerMul a.re scale).value a.den hpre.1 hden
  have h₄ := register_floor_cost (registerMul a.im scale).value a.den hpre.2.1 hden
  change _ ≤ 256*(W+2)^2 at h₃ h₄
  change _ ≤ 1024*(W+2)^2
  dsimp only [rawConversionCost]
  omega

attribute [local irreducible] RationalWorkBounds.rootRaw FFTBitCost.binaryRoot

theorem rootConversionBudget_polynomial (B k : ℕ) :
    1024*(rootBits B k+B+3)^2 ≤ 20000000*(B+k+79)^10 := by
  let S := B+k+79
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hS4 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have hB : B ≤ S^4 := by
    have : B ≤ S := by dsimp [S]; omega
    exact this.trans (by simpa using Nat.pow_le_pow_right hS (show 1≤4 by decide))
  have hbits : rootBits B k ≤ 128*S^4 := by
    apply (rootBits_polynomial B k).trans
    gcongr
    dsimp [S]; omega
  have hwidth : rootBits B k+B+3 ≤ 132*S^4 := by omega
  calc
    _ ≤ 1024*(132*S^4)^2 := Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hwidth 2)
    _ = 17842176*S^8 := by ring
    _ ≤ 17842176*S^10 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS (by decide))
    _ ≤ 20000000*S^10 := Nat.mul_le_mul_right _ (by omega)

/- Root conversion remains polynomial even with unreduced rational
numerators. The fixed-point scale is an already constructed public register. -/
theorem root_conversion_polynomial (B k j : ℕ) (hj : j < 2^k)
    (a : RawRegisters (rootRaw (2^k) j B))
    (scale : Register (FixedPointComplex.scaleZ B)) :
    rawConversionCost (B:=B) a scale ≤ 20000000*(B+k+79)^10 := by
  have hfit : RationalWorkBounds.Fits (rootRaw (2^k) j B) (rootBits B k) :=
    fits_rootRaw (L:=k) (N:=2^k) (j:=j) (B:=B) (show (2:ℕ)^k≤2^k from le_rfl) hj
  have hconvert : rawConversionCost (B:=B) a scale ≤ 1024*(rootBits B k+B+3)^2 :=
    rawConversionCost_bound (B:=B) (R:=rootBits B k) (r:=rootRaw (2^k) j B) a scale hfit
  exact hconvert.trans (rootConversionBudget_polynomial B k)



end ThinMatrix.BinaryCellCost

namespace ThinMatrix.BinaryArrayFFT
open FFTBitCost BinaryCellCost
attribute [local irreducible] RationalWorkBounds.rootRaw FFTBitCost.binaryRoot

theorem cellAdd_bitSteps {W : ℕ} (a b : Cell)
    (ha : FixedPointComplex.CellFits W a.view) (hb : FixedPointComplex.CellFits W b.view) :
    (cellAdd a b).bitSteps ≤ 512*(W+2)^2 := by
  have hr := register_add_cost a.reRegister b.reRegister ha.1 hb.1
  have hi := register_add_cost a.imRegister b.imRegister ha.2 hb.2
  dsimp only [cellAdd]
  omega

theorem cellMul_bitSteps {B W : ℕ} (s : Register ((2^B:ℕ):ℤ)) (a b : Cell)
    (ha : FixedPointComplex.CellFits W a.view) (hb : FixedPointComplex.CellFits W b.view) :
    (cellMul B s a b).bitSteps ≤ 2048*(max (2*W+1) (B+1)+2)^2 := by
  let s' : Register (FixedPointComplex.scaleZ B) := s.cast (by simp [FixedPointComplex.scaleZ])
  have h := cellMulCost_bound a.reRegister a.imRegister b.reRegister b.imRegister s' ha hb
  change _ ≤ _
  dsimp only [cellMulCost, cellMul] at h ⊢
  have heq : ∀ {z : ℤ} (r : Register z),
      (registerFloor r s').bitSteps = (registerFloor r s).bitSteps := by
    intro z r
    rfl
  simp only [heq] at h
  omega

@[simp] theorem cellConjugate_bitSteps (a : Cell) :
    (cellConjugate a).bitSteps = 1 := rfl


theorem embed_bitSteps {B W : ℕ} (s : Register ((2^B:ℕ):ℤ)) (a : Integer)
    (ha : BinaryCellCost.FP.Fits W a.view) :
    (embed B s a).bitSteps ≤ 256*(max W (B+1)+2)^2+2 := by
  let V := max W (B+1)
  have hs : BinaryCellCost.FP.Fits V ((2^B:ℕ):ℤ) := by
    simpa [FixedPointComplex.scaleZ] using
      fits_mono (FixedPointComplex.scale_bits B) (show B+1≤V from le_max_right _ _)
  have hm := register_mul_cost a.register s (fits_mono ha (le_max_left _ _)) hs
  dsimp only [embed]
  change _+2 ≤ _
  omega

theorem normalize_bitSteps {N W : ℕ} (d : Register (N:ℤ)) (a : Cell)
    (ha : FixedPointComplex.CellFits W a.view) (hN : BinaryCellCost.FP.Fits W (N:ℤ)) :
    (normalize N d a).bitSteps ≤ 512*(W+2)^2 := by
  have hr := register_floor_cost a.reRegister d ha.1 hN
  have hi := register_floor_cost a.imRegister d ha.2 hN
  dsimp only [normalize]
  omega

theorem scale_bitSteps (B : ℕ) :
    (scale B).bitSteps ≤ 2048*(B+1)*(B+3)^2 := by
  have htwo : (2:ℤ).natAbs ≤ 2^(B+1) := by
    change 2 ≤ (2:ℕ)^(B+1)
    exact (show 2^1 ≤ (2:ℕ)^(B+1) from Nat.pow_le_pow_right (by decide) (by omega))
  have hp : ∀ r ≤ B, ((2:ℤ)^r).natAbs ≤ 2^(B+1) := by
    intro r hr
    simp only [Int.natAbs_pow]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hwidth := intPowerTrace_width htwo hp
  have hprice := schedulePrice_width (intPowerTrace 2 B) (2*(B+1)+2) hwidth
  simp only [intPowerTrace_length] at hprice
  have hpower := binaryRegisterPower_cost (registerInput 2).value B
  have hsq : (2*(B+1)+2+2)^2 = 4*(B+3)^2 := by ring
  rw [hsq] at hprice
  have hpositive : 1 ≤ (B+3)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [scale]
  change 4+(binaryRegisterPower (registerInput 2).value B).bitSteps ≤ _
  nlinarith

theorem recover_bitSteps {B W : ℕ} (s : Register ((2^B:ℕ):ℤ)) (a : Cell)
    (ha : FixedPointComplex.CellFits W a.view) :
    (recover B s a).bitSteps ≤ 2048*(max W (B+1)+4)^2 := by
  let D := max W (B+1)
  let V := D+2
  have hWD : W ≤ D := le_max_left _ _
  have hBD : B+1 ≤ D := le_max_right _ _
  have hc : FixedPointComplex.CellFits D a.view :=
    ⟨fits_mono ha.1 hWD, fits_mono ha.2 hWD⟩
  have hp := ApproximateConvolution.recover_working_bits B D a.view (by omega) hc
  have htwo : BinaryCellCost.FP.Fits V (2:ℤ) :=
    fits_mono (magnitude_fits (R:=1) (by decide)) (by dsimp [V]; omega)
  have hs : BinaryCellCost.FP.Fits V ((2^B:ℕ):ℤ) := by
    simpa [FixedPointComplex.scaleZ] using
      fits_mono (FixedPointComplex.scale_bits B) (show B+1≤V by dsimp [V]; omega)
  have hreal : BinaryCellCost.FP.Fits V a.view.re := fits_mono hc.1 (by dsimp [V]; omega)
  have htwice : BinaryCellCost.FP.Fits V (2*a.view.re) := by
    apply fits_mono (W:=D+1) _ (by dsimp [V]; omega)
    simpa [two_mul] using add_fits hc.1 hc.1
  have h₁ := register_mul_cost (registerInput 2).value a.reRegister htwo hreal
  have h₂ := register_add_cost (registerMul (registerInput 2).value a.reRegister).value s htwice hs
  have h₃ := register_mul_cost (registerInput 2).value s htwo hs
  let den : Register ((2*2^B:ℕ):ℤ) :=
    (registerMul (registerInput 2).value s).value.cast (by push_cast; rfl)
  have hden : BinaryCellCost.FP.Fits V ((2*2^B:ℕ):ℤ) := by
    simpa [V,FixedPointComplex.scaleZ] using hp.2.1
  have hnum : BinaryCellCost.FP.Fits V (2*a.view.re+((2^B:ℕ):ℤ)) := by
    simpa [V,FixedPointComplex.scaleZ] using hp.1
  have h₄ := register_floor_cost
    (registerAdd (registerMul (registerInput 2).value a.reRegister).value s).value den hnum hden
  have hpositive : 1 ≤ (V+2)^2 := Nat.one_le_pow _ _ (by omega)
  change _ ≤ 2048*(V+2)^2
  dsimp only [recover]
  change 4+_+_+_+_ ≤ _
  have heq : (registerFloor
      (registerAdd (registerMul (registerInput 2).value a.reRegister).value s).value den).bitSteps =
      (registerFloor
      (registerAdd (registerMul (registerInput 2).value a.reRegister).value s).value
      ((registerMul (registerInput 2).value s).value.cast (by push_cast; rfl))).bitSteps := rfl
  rw [heq] at h₄
  omega

end ThinMatrix.BinaryArrayFFT


namespace ThinMatrix.BinaryRootConversion
open FFTBitCost RationalWorkBounds BinaryCellCost

attribute [local irreducible] RationalWorkBounds.rootRaw FFTBitCost.binaryRoot

theorem conversion_width_polynomial (B k : ℕ) :
    1024*(rootBits B k+B+3)^2 ≤ 20000000*(B+k+79)^10 := by
  let S := B+k+79
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hS4 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have hB : B ≤ S^4 := by
    have : B ≤ S := by dsimp [S]; omega
    exact this.trans (by simpa using Nat.pow_le_pow_right hS (show 1≤4 by decide))
  have hbits : rootBits B k ≤ 128*S^4 := by
    apply (rootBits_polynomial B k).trans
    gcongr
    dsimp [S]; omega
  have hwidth : rootBits B k+B+3 ≤ 132*S^4 := by omega
  calc
    1024*(rootBits B k+B+3)^2 ≤ 1024*(132*S^4)^2 :=
      Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hwidth 2)
    _ = 17842176*S^8 := by ring
    _ ≤ 17842176*S^10 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS (by decide))
    _ ≤ 20000000*S^10 := Nat.mul_le_mul_right _ (by norm_num)

theorem raw_conversion_polynomial {r : Raw} (B k : ℕ)
    (a : RawRegisters r) (scale : Register (FixedPointComplex.scaleZ B))
    (hr : RationalWorkBounds.Fits r (rootBits B k)) :
    rawConversionCost a scale ≤ 20000000*(B+k+79)^10 :=
  (rawConversionCost_bound a scale hr).trans (conversion_width_polynomial B k)

/-- The direct conversion counter uses the same scale-register bits. -/
def directConversionCost {B : ℕ} {r : Raw} (a : RawRegisters r)
    (s : Register ((2^B:ℕ):ℤ)) : ℕ :=
  let reScaled := registerMul a.re s
  let imScaled := registerMul a.im s
  reScaled.bitSteps+imScaled.bitSteps+
    (registerFloor reScaled.value a.den).bitSteps+
    (registerFloor imScaled.value a.den).bitSteps

theorem direct_conversion_eq {B : ℕ} {r : Raw} (a : RawRegisters r)
    (s : Register ((2^B:ℕ):ℤ)) :
    directConversionCost a s =
      rawConversionCost (B:=B) a (s.cast (by simp [FixedPointComplex.scaleZ])) := by
  rfl

theorem twiddle_cost_decompose (B k : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (inverse : Bool) (j : ℕ) :
    (BinaryArrayFFT.twiddle B k s inverse j).bitSteps =
      (binaryRoot (2^k) j B).bitSteps +
        directConversionCost (binaryRoot (2^k) j B).value s +
        (if inverse then 1 else 0) := by
  cases inverse <;>
    simp only [BinaryArrayFFT.twiddle, Bool.false_eq_true, if_false, if_true,
      BinaryArrayFFT.cellConjugate_bitSteps, directConversionCost] <;>
    omega

theorem twiddle_bitSteps (B k j : ℕ) (s : Register ((2^B:ℕ):ℤ)) (inverse : Bool)
    (hj : j < 2^k) :
    (BinaryArrayFFT.twiddle B k s inverse j).bitSteps ≤ 8589934592*(B+k+79)^10 := by
  have hfit : RationalWorkBounds.Fits (rootRaw (2^k) j B) (rootBits B k) :=
    fits_rootRaw (L:=k) (N:=2^k) (j:=j) (B:=B) le_rfl hj
  have hraw := raw_conversion_polynomial B k (binaryRoot (2^k) j B).value
    (s.cast (by simp [FixedPointComplex.scaleZ])) hfit
  rw [← direct_conversion_eq] at hraw
  have hroot := binaryRoot_polynomial (L:=k) (B:=B) le_rfl hj
  have hS : 1 ≤ (B+k+79)^10 := Nat.one_le_pow _ _ (by omega)
  rw [twiddle_cost_decompose]
  cases inverse <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega


end ThinMatrix.BinaryRootConversion



namespace ThinMatrix.BinaryArrayFFT
open scoped BigOperators
open FFTBitCost

/-- Semantic value of a binary-backed transform, at its actual array locator. -/
theorem fft_getD_view_approx (B k : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (inverse : Bool) (a : Array Cell) (j : ℕ) :
    ((fft B s inverse k a).value.getD j zeroCell).view =
      (ApproximateConvolution.fft B inverse k (fun i => (a.getD i zeroCell).view)).value.getD j
        ApproximateConvolution.zero := by
  rw [← viewCells_getD, fft_view, ← ArrayFFT.getD_toList, ArrayFFT.fft_toList]
  simp only [viewCells_getD]

/-- All child FFTs share the top-stage magnitude allowance, justified by
semantic error propagation rather than an assumed runtime-size condition. -/
theorem fft_actual_subcall_fits (B l k A : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (inverse : Bool) (a : Array Cell) (x : ℕ → ℂ) (E : ℝ)
    (hl : l ≤ k) (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1/2)
    (ha : ∀ i < 2^l, ‖x i‖ ≤ (A:ℝ))
    (hx : ∀ i < 2^l, ‖FixedPointComplex.decode B (a.getD i zeroCell).view - x i‖ ≤ E)
    (hsmall : ApproximateConvolution.fftError B k A E ≤ 1)
    (j : ℕ) (hj : j < 2^l) :
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2^k*A+2))
      ((fft B s inverse l a).value.getD j zeroCell).view := by
  rw [fft_getD_view_approx]
  apply FixedPointComplex.decoded_bits
  have hn := ApproximateConvolution.fft_decoded_norm_bound B l inverse
    (fun i => (a.getD i zeroCell).view) x A E (Nat.cast_nonneg _) hE heps ha hx j hj
  have hm := ApproximateConvolution.fftError_mono_depth B l k A E (Nat.cast_nonneg _) hE hl
  have hp : (2:ℝ)^l*A ≤ 2^k*A :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (Nat.cast_nonneg A)
  push_cast
  linarith

/-- Combined multiplication and addition charge. The product numerator is
allowed twice the operand width before its rounded quotient is reused. -/
theorem butterfly_bitSteps {B W : ℕ} (s : Register ((2^B:ℕ):ℤ)) (even root odd : Cell)
    (he : FixedPointComplex.CellFits W even.view)
    (hr : FixedPointComplex.CellFits W root.view)
    (ho : FixedPointComplex.CellFits W odd.view) :
    (cellMul B s root odd).bitSteps +
      (cellAdd even (cellMul B s root odd).value).bitSteps ≤
        2560*(max (2*W+1) (B+1)+2)^2 := by
  have hm := cellMul_bitSteps s root odd hr ho
  have hp := (BinaryCellCost.cell_mul_working_fits (B:=B) hr ho).2.2.2.2.2.2
  rw [← cellMul_view B s root odd] at hp
  have he' : FixedPointComplex.CellFits (2*W+1) even.view :=
    ⟨BinaryCellCost.fits_mono he.1 (by omega), BinaryCellCost.fits_mono he.2 (by omega)⟩
  have hadd := cellAdd_bitSteps even (cellMul B s root odd).value he' hp
  have hadd' : (cellAdd even (cellMul B s root odd).value).bitSteps ≤
      512*(max (2*W+1) (B+1)+2)^2 := by
    apply hadd.trans
    gcongr
    exact le_max_left _ _
  omega

/-- Global callback envelope for the actual binary FFT. -/
def actualFFTCallback (B k A : ℕ) : ℕ :=
  8589934592*(B+k+79)^10 +
    2560*(max (2*FixedPointComplex.storedBits B (2^k*A+2)+1) (B+1)+2)^2

theorem tabulate_bitSteps_eq_scratch {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).bitSteps = ∑ j : Fin N, (f j).bitSteps := by
  have aux (xs : List (BinaryResult α)) (z : ℕ) :
      xs.foldl (fun cost c => cost+c.bitSteps) z = z+(xs.map (fun c => c.bitSteps)).sum := by
    induction xs generalizing z with
    | nil => simp
    | cons x xs ih => simpa [List.foldl_cons, Nat.add_assoc] using ih (z+x.bitSteps)
  change (Array.ofFn f).foldl (fun cost c => cost+c.bitSteps) 0 = _
  rw [← Array.foldl_toList, aux]
  simp [List.map_ofFn, List.sum_ofFn]

theorem tabulate_bitSteps_le_scratch {α : Type} (N P : ℕ) (f : Fin N → BinaryResult α)
    (hf : ∀ i, (f i).bitSteps ≤ P) :
    (tabulate N f).bitSteps ≤ N*P := by
  rw [tabulate_bitSteps_eq_scratch]
  calc
    _ ≤ ∑ _i : Fin N, P := Finset.sum_le_sum (fun i _ => hf i)
    _ = N*P := by simp

/-- Actual recursion cost: no intermediate-size assumption occurs in the
statement; every cell bound follows from input semantics and certified error. -/
theorem fft_bitSteps_of_small (B l k A : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (inverse : Bool) (a : Array Cell) (x : ℕ → ℂ) (E : ℝ)
    (hl : l ≤ k) (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1/2)
    (ha : ∀ i < 2^l, ‖x i‖ ≤ (A:ℝ))
    (hx : ∀ i < 2^l, ‖FixedPointComplex.decode B (a.getD i zeroCell).view - x i‖ ≤ E)
    (hsmall : ApproximateConvolution.fftError B k A E ≤ 1) :
    (fft B s inverse l a).bitSteps ≤ l*2^l*actualFFTCallback B k A := by
  induction l generalizing a x with
  | zero => simp [fft]
  | succ l ih =>
      let evenInput := Array.ofFn (fun i : Fin (2^l) => a.getD (2*i.val) zeroCell)
      let oddInput := Array.ofFn (fun i : Fin (2^l) => a.getD (2*i.val+1) zeroCell)
      have hei (i : ℕ) (hi : i < 2^l) : 2*i < 2^(l+1) := by rw [pow_succ]; omega
      have hoi (i : ℕ) (hi : i < 2^l) : 2*i+1 < 2^(l+1) := by rw [pow_succ]; omega
      have hea : ∀ i < 2^l, ‖x (2*i)‖ ≤ (A:ℝ) := fun i hi => ha _ (hei i hi)
      have hoa : ∀ i < 2^l, ‖x (2*i+1)‖ ≤ (A:ℝ) := fun i hi => ha _ (hoi i hi)
      have hex : ∀ i < 2^l,
          ‖FixedPointComplex.decode B (evenInput.getD i zeroCell).view-x (2*i)‖ ≤ E := by
        intro i hi
        dsimp [evenInput]
        rw [ArrayFFT.getD_ofFn _ i hi]
        exact hx _ (hei i hi)
      have hox : ∀ i < 2^l,
          ‖FixedPointComplex.decode B (oddInput.getD i zeroCell).view-x (2*i+1)‖ ≤ E := by
        intro i hi
        dsimp [oddInput]
        rw [ArrayFFT.getD_ofFn _ i hi]
        exact hx _ (hoi i hi)
      have he := ih evenInput (fun i => x (2*i)) (by omega) hea hex
      have ho := ih oddInput (fun i => x (2*i+1)) (by omega) hoa hox
      let W := FixedPointComplex.storedBits B (2^k*A+2)
      let roots := tabulate (2^(l+1)) (fun j => twiddle B (l+1) s inverse j.val)
      have roots_bound : roots.bitSteps ≤
          2^(l+1)*(8589934592*(B+k+79)^10) := by
        apply tabulate_bitSteps_le_scratch
        intro j
        apply (BinaryRootConversion.twiddle_bitSteps B (l+1) j.val s inverse j.isLt).trans
        gcongr
      have node_bound :
          (tabulate (2^(l+1)) (fun j =>
            let index := j.val % 2^l
            let product := cellMul B s (roots.value.getD j.val zeroCell)
              ((fft B s inverse l oddInput).value.getD index zeroCell)
            let sum := cellAdd ((fft B s inverse l evenInput).value.getD index zeroCell) product.value
            (⟨sum.value, product.bitSteps+sum.bitSteps⟩ : BinaryResult Cell))).bitSteps ≤
          2^(l+1)*(2560*(max (2*W+1) (B+1)+2)^2) := by
        apply tabulate_bitSteps_le_scratch
        intro j
        have hj : j.val % 2^l < 2^l := Nat.mod_lt _ (by positivity)
        have hef := fft_actual_subcall_fits B l k A s inverse evenInput
          (fun i => x (2*i)) E (by omega) hE heps hea hex hsmall _ hj
        have hof := fft_actual_subcall_fits B l k A s inverse oddInput
          (fun i => x (2*i+1)) E (by omega) hE heps hoa hox hsmall _ hj
        have hroot : FixedPointComplex.CellFits W (roots.value.getD j.val zeroCell).view := by
          dsimp [roots]
          rw [tabulate_getD _ _ j.val j.isLt, twiddle_view]
          apply FixedPointComplex.decoded_bits
          exact (ApproximateConvolution.twiddle_norm_le_two B (l+1) inverse j.val j.isLt heps).trans
            (by push_cast; nlinarith [show (0:ℝ) ≤ 2^k*(A:ℝ) by positivity])
        exact butterfly_bitSteps s _ _ _ hef hroot hof
      change (fft B s inverse l evenInput).bitSteps +
        (fft B s inverse l oddInput).bitSteps + roots.bitSteps + _ ≤ _
      calc
        _ ≤ l*2^l*actualFFTCallback B k A + l*2^l*actualFFTCallback B k A +
            2^(l+1)*(8589934592*(B+k+79)^10) +
            2^(l+1)*(2560*(max (2*W+1) (B+1)+2)^2) := by
          exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add he ho) roots_bound) node_bound
        _ = (l+1)*2^(l+1)*actualFFTCallback B k A := by
          dsimp [actualFFTCallback,W]
          rw [pow_succ]
          ring

/-- Exact semantic source replacement at an actual array transform. -/
theorem fft_getD_view_eq (B k : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (inverse : Bool) (a : Array Cell) (x : ℕ → FixedPointComplex.Cell)
    (ha : ∀ i < 2^k, (a.getD i zeroCell).view = x i) (j : ℕ) :
    ((fft B s inverse k a).value.getD j zeroCell).view =
      (ApproximateConvolution.fft B inverse k x).value.getD j ApproximateConvolution.zero := by
  rw [← viewCells_getD, fft_view, ← ArrayFFT.getD_toList,
    ArrayFFT.fft_toList_eq B k inverse (viewCells a) x]
  intro i hi
  simpa only [viewCells_getD] using ha i hi

/-- The forward transform input is the actual register-scaled integer array. -/
theorem forward_fft_bitSteps (k A : ℕ)
    (s : Register ((2^(ApproximateConvolution.convPrecision k A):ℕ):ℤ))
    (a : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, ‖((a.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ)) :
    let B := ApproximateConvolution.convPrecision k A
    (fft B s false k (embedArray B (2^k) s a).value).bitSteps ≤
      k*2^k*actualFFTCallback B k A := by
  dsimp only
  apply fft_bitSteps_of_small _ k k A s false _
    (fun i => ((a.getD i zeroInteger).view:ℂ)) 0 le_rfl (by norm_num)
    (ApproximateConvolution.convPrecision_eps_le k A) ha
    (fun i hi => ?_)
    (ApproximateConvolution.convPrecision_intermediate_errors k A hA).1
  rw [embedArray, tabulate_getD _ _ i hi, embed_view, ApproximateConvolution.decode_embed]
  simp

/-- Frequency source in the inverse is the product of the two actual forward
arrays, with no uncharged semantic conversion. -/
theorem actual_frequencies_view (B k : ℕ) (s : Register ((2^B:ℕ):ℤ))
    (a b : Array Integer) (j : ℕ) (hj : j < 2^k) :
    ((pointwiseArray B (2^k) s
      (fft B s false k (embedArray B (2^k) s a).value).value
      (fft B s false k (embedArray B (2^k) s b).value).value).value.getD j zeroCell).view =
    (ApproximateConvolution.frequencyCells B k
      (fun i => (a.getD i zeroInteger).view) (fun i => (b.getD i zeroInteger).view)).getD j
      ApproximateConvolution.zero := by
  rw [pointwiseArray, tabulate_getD _ _ j hj, cellMul_view]
  rw [fft_getD_view_eq B k s false _
    (fun i => ApproximateConvolution.embed B (a.getD i zeroInteger).view)
    (by intro i hi; rw [embedArray, tabulate_getD _ _ i hi, embed_view])]
  rw [fft_getD_view_eq B k s false _
    (fun i => ApproximateConvolution.embed B (b.getD i zeroInteger).view)
    (by intro i hi; rw [embedArray, tabulate_getD _ _ i hi, embed_view])]
  rw [ApproximateConvolution.frequencyCells, ApproximateConvolution.pointwise_getD B (2^k) _ _ j hj]

/-- The inverse transform is priced on the actual pointwise products of the
actual integer forward transforms at the certified convolution precision. -/
theorem inverse_fft_bitSteps (k A : ℕ)
    (s : Register ((2^(ApproximateConvolution.convPrecision k A):ℕ):ℤ))
    (a b : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, ‖((a.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ))
    (hb : ∀ i < 2^k, ‖((b.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ)) :
    let B := ApproximateConvolution.convPrecision k A
    (fft B s true k (pointwiseArray B (2^k) s
      (fft B s false k (embedArray B (2^k) s a).value).value
      (fft B s false k (embedArray B (2^k) s b).value).value).value).bitSteps ≤
      k*2^k*actualFFTCallback B k (2^(2*k)*A^2) := by
  let B := ApproximateConvolution.convPrecision k A
  let f := fun i => FastConvolution.radixFFT k (ApproximateConvolution.omega k false)
      (fun t => ((a.getD t zeroInteger).view:ℂ)) i *
    FastConvolution.radixFFT k (ApproximateConvolution.omega k false)
      (fun t => ((b.getD t zeroInteger).view:ℂ)) i
  have hE : 0 ≤ ApproximateConvolution.frequencyError B k A := by
    unfold ApproximateConvolution.frequencyError ApproximateConvolution.forwardError
      ApproximateConvolution.fftError
    have he := (FixedPointComplex.eps_pos B).le
    positivity
  apply fft_bitSteps_of_small B k k (2^(2*k)*A^2) s true _ f
    (ApproximateConvolution.frequencyError B k A) le_rfl hE
    (ApproximateConvolution.convPrecision_eps_le k A)
  · intro i hi
    exact ApproximateConvolution.frequency_exact_norm k A _ _ ha hb i
  · intro i hi
    rw [actual_frequencies_view B k s a b i hi]
    exact ApproximateConvolution.frequencyCells_error B k _ _ A (Nat.cast_nonneg _)
      (ApproximateConvolution.convPrecision_eps_le k A) ha hb i hi
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (ApproximateConvolution.convPrecision_intermediate_errors k A hA).2.2

/-- Two guard units are covered by the same conservative logarithmic stage
allowance as the semantic FFT outputs. -/
theorem stage_storedBits_plus_two_linear (B k A : ℕ) :
    FixedPointComplex.storedBits B (2^(3*k)*A^2+2) ≤ B+3*k+2*A.log2+4 := by
  have ha : A < 2^(A.log2+1) := Nat.lt_log2_self
  have hs : A^2 < (2^(A.log2+1))^2 := by nlinarith
  have hm := Nat.mul_lt_mul_of_pos_left hs (by positivity : 0 < (2:ℕ)^(3*k))
  have hp : 2^(3*k)*(2^(A.log2+1))^2 = 2^(3*k+2*A.log2+2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hp] at hm
  have htwo : 2 < (2:ℕ)^(3*k+2*A.log2+2) := by
    have h := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide)
      (show 2≤3*k+2*A.log2+2 by omega)
    norm_num at h ⊢
    omega
  have hn : 2^(3*k)*A^2+2 < 2^(3*k+2*A.log2+3) := by
    have he : (2:ℕ)^(3*k+2*A.log2+3) = 2^(3*k+2*A.log2+2)*2 := by
      rw [show 3*k+2*A.log2+3 = (3*k+2*A.log2+2)+1 by omega, pow_succ]
    rw [he]
    omega
  have hl := (Nat.log2_lt (by positivity : 2^(3*k)*A^2+2 ≠ 0)).mpr hn
  unfold FixedPointComplex.storedBits
  omega

theorem actualFFTCallback_convPrecision (k A : ℕ) :
    actualFFTCallback (ApproximateConvolution.convPrecision k A) k (2^(2*k)*A^2) ≤
      2305843009213693952*(k+A.log2+100)^10 := by
  let B := ApproximateConvolution.convPrecision k A
  let S := k+A.log2+100
  have hS : 1≤S := by dsimp [S]; omega
  have hB : B≤5*S := by
    have := ApproximateConvolution.convPrecision_linear k A
    dsimp [B,S]
    omega
  have hroot : B+k+79≤6*S := by dsimp [S] at *; omega
  have hwidth : FixedPointComplex.storedBits B (2^k*(2^(2*k)*A^2)+2) ≤ 8*S := by
    have hw := stage_storedBits_plus_two_linear B k A
    have heq : 2^k*(2^(2*k)*A^2) = 2^(3*k)*A^2 := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [heq]
    dsimp [S] at *
    omega
  have hmax : max (2*FixedPointComplex.storedBits B (2^k*(2^(2*k)*A^2)+2)+1) (B+1)+2 ≤ 20*S := by
    omega
  have hpow : S^2≤S^10 := Nat.pow_le_pow_right hS (by decide)
  unfold actualFFTCallback
  change 8589934592*(B+k+79)^10 +
    2560*(max (2*FixedPointComplex.storedBits B (2^k*(2^(2*k)*A^2)+2)+1) (B+1)+2)^2 ≤ _
  calc
    _ ≤ 8589934592*(6*S)^10+2560*(20*S)^2 := by gcongr
    _ = 519400496868360192*S^10+1024000*S^2 := by ring
    _ ≤ 519400496868360192*S^10+1024000*S^10 := by omega
    _ ≤ 2305843009213693952*S^10 := by omega

theorem log2_mono_scratch {m n : ℕ} (h : m≤n) : m.log2≤n.log2 := by
  by_cases hm : m=0
  · simp [hm]
  have hp : m<2^(n.log2+1) := h.trans_lt Nat.lt_log2_self
  have hl := (Nat.log2_lt hm).mpr hp
  omega

theorem actualFFTCallback_mono (B k A C : ℕ) (h : A≤C) :
    actualFFTCallback B k A≤actualFFTCallback B k C := by
  have hm : 2^k*A+2≤2^k*C+2 := by gcongr
  have hl := log2_mono_scratch hm
  unfold actualFFTCallback FixedPointComplex.storedBits
  gcongr

theorem forward_fft_bitSteps_polynomial (k A : ℕ)
    (s : Register ((2^(ApproximateConvolution.convPrecision k A):ℕ):ℤ))
    (a : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, ‖((a.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ)) :
    let B := ApproximateConvolution.convPrecision k A
    (fft B s false k (embedArray B (2^k) s a).value).bitSteps ≤
      k*2^k*(2305843009213693952*(k+A.log2+100)^10) := by
  apply (forward_fft_bitSteps k A s a hA ha).trans
  apply Nat.mul_le_mul_left
  have hlarge : A≤2^(2*k)*A^2 := by
    have hpow : 1≤(2:ℕ)^(2*k) := Nat.one_le_pow _ _ (by decide)
    nlinarith
  exact (actualFFTCallback_mono _ k A (2^(2*k)*A^2) hlarge).trans
    (actualFFTCallback_convPrecision k A)

theorem inverse_fft_bitSteps_polynomial (k A : ℕ)
    (s : Register ((2^(ApproximateConvolution.convPrecision k A):ℕ):ℤ))
    (a b : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, ‖((a.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ))
    (hb : ∀ i < 2^k, ‖((b.getD i zeroInteger).view:ℂ)‖ ≤ (A:ℝ)) :
    let B := ApproximateConvolution.convPrecision k A
    (fft B s true k (pointwiseArray B (2^k) s
      (fft B s false k (embedArray B (2^k) s a).value).value
      (fft B s false k (embedArray B (2^k) s b).value).value).value).bitSteps ≤
      k*2^k*(2305843009213693952*(k+A.log2+100)^10) := by
  exact (inverse_fft_bitSteps k A s a b hA ha hb).trans
    (Nat.mul_le_mul_left _ (actualFFTCallback_convPrecision k A))

end ThinMatrix.BinaryArrayFFT


/-! Reusable array-based tabulation and radix-two resource templates.
The counter is a ledger for callback bit circuits. Array map/fold control is
separate from these callback bit steps. The executable definition does not
convert arrays to lists and evaluates each callback once. -/
namespace ThinMatrix.BinaryArrayCosts
open scoped BigOperators
open FFTBitCost

/-- Store each callback result once, project its stored value, and fold its
stored counter. No callback is rerun by the value or cost projections. -/
def tabulate {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) : BinaryResult (Array α) :=
  let evaluated := Array.ofFn f
  ⟨evaluated.map BinaryResult.value,
    evaluated.foldl (fun total result => total+result.bitSteps) 0⟩

@[simp] theorem tabulate_value {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).value = Array.ofFn (fun i => (f i).value) := by
  simp only [tabulate, Array.map_ofFn, Function.comp_def]

@[simp] theorem tabulate_size {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).value.size = N := by simp

theorem tabulate_getD {α : Type} (N : ℕ) (f : Fin N → BinaryResult α)
    (i : ℕ) (hi : i < N) (d : α) :
    (tabulate N f).value.getD i d = (f ⟨i,hi⟩).value := by
  rw [tabulate_value, ArrayFFT.getD_ofFn _ i hi]

/-- List conversion appears only in this specification lemma. -/
theorem array_fold_cost_eq {α : Type} (a : Array α) (cost : α → ℕ) :
    a.foldl (fun total x => total+cost x) 0 = (a.toList.map cost).sum := by
  rw [← Array.foldl_toList]
  rw [← List.foldl_map]
  exact (List.sum_eq_foldl).symm

theorem list_sum_cost_bound {α : Type} (l : List α) (cost : α → ℕ) (C : ℕ)
    (hC : ∀ x ∈ l, cost x ≤ C) : (l.map cost).sum ≤ l.length*C := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hC a (by simp)
      have hl := ih (fun x hx => hC x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith


/-- Finite-sum specification of array accumulation, used only in proofs. -/
theorem array_ofFn_fold_cost {α : Type} {N : ℕ}
    (f : Fin N → α) (cost : α → ℕ) :
    (Array.ofFn f).foldl (fun total x => total+cost x) 0 =
      ∑ i : Fin N, cost (f i) := by
  rw [← Array.foldl_toList, Array.toList_ofFn, ← List.foldl_map,
    ← List.sum_eq_foldl, List.map_ofFn, List.sum_ofFn]
  rfl

theorem tabulate_bitSteps_eq {α : Type} (N : ℕ) (f : Fin N → BinaryResult α) :
    (tabulate N f).bitSteps = ∑ i : Fin N, (f i).bitSteps :=
  array_ofFn_fold_cost f BinaryResult.bitSteps

/-- Bound for a genuine Array.foldl over stored results. -/
theorem array_fold_cost_bound {α : Type} (a : Array α) (cost : α → ℕ) (C : ℕ)
    (hC : ∀ x ∈ a, cost x ≤ C) :
    a.foldl (fun total x => total+cost x) 0 ≤ a.size*C := by
  rw [array_fold_cost_eq]
  have h := list_sum_cost_bound a.toList cost C (by simpa using hC)
  simpa using h

theorem tabulate_bitSteps_bound {α : Type} (N : ℕ)
    (f : Fin N → BinaryResult α) (C : ℕ) (hC : ∀ i, (f i).bitSteps ≤ C) :
    (tabulate N f).bitSteps ≤ N*C := by
  change (Array.ofFn f).foldl (fun total result => total+result.bitSteps) 0 ≤ N*C
  have h := array_fold_cost_bound (Array.ofFn f) BinaryResult.bitSteps C (by
    intro x hx
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
    exact hC i)
  simpa using h

/-- A radix-two recurrence with zero-cost leaves and two possibly different
stored children gives the usual `k*2^k*C` circuit bound. -/
theorem radixTwo_cost_bound {α : Type} (cost : ℕ → α → ℕ)
    (left right : ℕ → α → α) (C : ℕ)
    (hzero : ∀ a, cost 0 a = 0)
    (hrec : ∀ k a, cost (k+1) a ≤ cost k (left k a)+cost k (right k a)+2^(k+1)*C)
    (k : ℕ) (a : α) : cost k a ≤ k*2^k*C := by
  induction k generalizing a with
  | zero => simp [hzero]
  | succ k ih =>
      calc
        cost (k+1) a ≤ cost k (left k a)+cost k (right k a)+2^(k+1)*C := hrec k a
        _ ≤ k*2^k*C+k*2^k*C+2^(k+1)*C := by
          exact Nat.add_le_add_right (Nat.add_le_add (ih _) (ih _)) _
        _ = (k+1)*2^(k+1)*C := by rw [pow_succ]; ring

/-- The same estimate only needs node estimates below the requested height.
This allows a uniform scalar-unit budget `C` chosen from the top height. -/
theorem radixTwo_cost_bound_upto {α : Type} (cost : ℕ → α → ℕ)
    (left right : ℕ → α → α) (C H : ℕ)
    (hzero : ∀ a, cost 0 a = 0)
    (hrec : ∀ k < H, ∀ a, cost (k+1) a ≤
      cost k (left k a)+cost k (right k a)+2^(k+1)*C)
    (k : ℕ) (hk : k ≤ H) (a : α) : cost k a ≤ k*2^k*C := by
  induction k generalizing a with
  | zero => simp [hzero]
  | succ k ih =>
      have hkH : k < H := by omega
      have hk' : k ≤ H := by omega
      calc
        cost (k+1) a ≤ cost k (left k a)+cost k (right k a)+2^(k+1)*C := hrec k hkH a
        _ ≤ k*2^k*C+k*2^k*C+2^(k+1)*C := by
          exact Nat.add_le_add_right (Nat.add_le_add (ih hk' _) (ih hk' _)) _
        _ = (k+1)*2^(k+1)*C := by rw [pow_succ]; ring


/-- Apply the generic stored-tabulation estimate to the actual lowering. -/
theorem actual_tabulate_bitSteps_bound {α : Type} (N : ℕ)
    (f : Fin N → BinaryResult α) (C : ℕ) (hC : ∀ i, (f i).bitSteps ≤ C) :
    (BinaryArrayFFT.tabulate N f).bitSteps ≤ N*C := by
  exact tabulate_bitSteps_bound N f C hC

namespace Actual
open BinaryArrayFFT

def evenInput (k : ℕ) (a : Array Cell) : Array Cell :=
  Array.ofFn (fun i : Fin (2^k) => a.getD (2*i.val) zeroCell)

def oddInput (k : ℕ) (a : Array Cell) : Array Cell :=
  Array.ofFn (fun i : Fin (2^k) => a.getD (2*i.val+1) zeroCell)

def butterfly (B k : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (a : Array Cell) (j : Fin (2^(k+1))) : BinaryResult Cell :=
  let even := fft B s inverse k (evenInput k a)
  let odd := fft B s inverse k (oddInput k a)
  let roots := BinaryArrayFFT.tabulate (2^(k+1)) (fun j => twiddle B (k+1) s inverse j.val)
  let index := j.val % 2^k
  let product := cellMul B s (roots.value.getD j.val zeroCell) (odd.value.getD index zeroCell)
  let sum := cellAdd (even.value.getD index zeroCell) product.value
  ⟨sum.value, product.bitSteps+sum.bitSteps⟩

/-- Exact counter equation for the actual stored FFT, with no cost assumption. -/
theorem fft_node_bitSteps (B k : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (a : Array Cell) :
    (fft B s inverse (k+1) a).bitSteps =
      (fft B s inverse k (evenInput k a)).bitSteps+
      (fft B s inverse k (oddInput k a)).bitSteps+
      (BinaryArrayFFT.tabulate (2^(k+1))
        (fun j => twiddle B (k+1) s inverse j.val)).bitSteps+
      (BinaryArrayFFT.tabulate (2^(k+1)) (butterfly B k s inverse a)).bitSteps := rfl

/-- Bounds exactly the callbacks run at one actual node. -/
def NodeCallbacksBound (B k : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (a : Array Cell) (R C : ℕ) : Prop :=
  (∀ j : Fin (2^(k+1)), (twiddle B (k+1) s inverse j.val).bitSteps ≤ R) ∧
  (∀ j : Fin (2^(k+1)), (butterfly B k s inverse a j).bitSteps ≤ C)

theorem fft_node_bitSteps_bound (B k : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (a : Array Cell) (R C : ℕ)
    (h : NodeCallbacksBound B k s inverse a R C) :
    (fft B s inverse (k+1) a).bitSteps ≤
      (fft B s inverse k (evenInput k a)).bitSteps+
      (fft B s inverse k (oddInput k a)).bitSteps+2^(k+1)*(R+C) := by
  have hr := actual_tabulate_bitSteps_bound (2^(k+1))
    (fun j => twiddle B (k+1) s inverse j.val) R h.1
  have hc := actual_tabulate_bitSteps_bound (2^(k+1)) (butterfly B k s inverse a) C h.2
  rw [fft_node_bitSteps]
  nlinarith

/-- Uniform callback estimates over this particular stored recursion tree.
No estimate for unrelated/unbounded arrays is required. -/
def CallTreeBound (B : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (R C : ℕ) : ℕ → Array Cell → Prop
  | 0, _ => True
  | k+1, a => CallTreeBound B s inverse R C k (evenInput k a) ∧
      CallTreeBound B s inverse R C k (oddInput k a) ∧
      NodeCallbacksBound B k s inverse a R C

/-- Actual binary FFT circuit work from local bounds on every callback it runs. -/
theorem fft_bitSteps_uniform (B k : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (a : Array Cell) (R C : ℕ)
    (h : CallTreeBound B s inverse R C k a) :
    (fft B s inverse k a).bitSteps ≤ k*2^k*(R+C) := by
  induction k generalizing a with
  | zero => simp [fft]
  | succ k ih =>
      calc
        (fft B s inverse (k+1) a).bitSteps ≤
          (fft B s inverse k (evenInput k a)).bitSteps+
          (fft B s inverse k (oddInput k a)).bitSteps+2^(k+1)*(R+C) :=
            fft_node_bitSteps_bound B k s inverse a R C h.2.2
        _ ≤ k*2^k*(R+C)+k*2^k*(R+C)+2^(k+1)*(R+C) :=
          Nat.add_le_add_right (Nat.add_le_add (ih _ h.1) (ih _ h.2.1)) _
        _ = (k+1)*2^(k+1)*(R+C) := by rw [pow_succ]; ring

/-- An input invariant can discharge the actual recursion-tree premise.
The invariant may depend on the remaining depth and the original parameters. -/
theorem callTreeBound_of_invariant (B : ℕ) (s : Register ((2^B : ℕ) : ℤ))
    (inverse : Bool) (R C : ℕ) (I : ℕ → Array Cell → Prop)
    (hchildren : ∀ k a, I (k+1) a → I k (evenInput k a) ∧ I k (oddInput k a))
    (hnodes : ∀ k a, I (k+1) a → NodeCallbacksBound B k s inverse a R C)
    (k : ℕ) (a : Array Cell) (ha : I k a) :
    CallTreeBound B s inverse R C k a := by
  induction k generalizing a with
  | zero => trivial
  | succ k ih =>
      exact ⟨ih _ (hchildren k a ha).1, ih _ (hchildren k a ha).2, hnodes k a ha⟩

end Actual


theorem actual_tabulate_bitSteps_eq {α : Type} (N : ℕ)
    (f : Fin N → BinaryResult α) :
    (BinaryArrayFFT.tabulate N f).bitSteps = ∑ i : Fin N, (f i).bitSteps :=
  array_ofFn_fold_cost f BinaryResult.bitSteps

namespace Actual
open BinaryArrayFFT

/-- Exact decomposition of the full three-transform convolution circuit. -/
theorem convolutionCore_bitSteps_eq (B k : ℕ)
    (s : Register ((2^B : ℕ) : ℤ)) (a b : Array Integer) :
    let N : ℕ := 2^k
    let denominator := registerInput (N : ℤ)
    let leftInput := embedArray B N s a
    let rightInput := embedArray B N s b
    let left := fft B s false k leftInput.value
    let right := fft B s false k rightInput.value
    let frequencies := pointwiseArray B N s left.value right.value
    let inverse := fft B s true k frequencies.value
    let output := normalizeArray N denominator.value inverse.value
    (convolutionCore B k s a b).bitSteps = denominator.bitSteps+
      leftInput.bitSteps+rightInput.bitSteps+left.bitSteps+right.bitSteps+
      frequencies.bitSteps+inverse.bitSteps+output.bitSteps := rfl

/-- Public scale construction is charged once outside the convolution core. -/
theorem convolution_bitSteps_bound (B k S C : ℕ) (a b : Array Integer)
    (hscale : (scale B).bitSteps ≤ S)
    (hcore : (convolutionCore B k (scale B).value a b).bitSteps ≤ C) :
    (convolution B k a b).bitSteps ≤ S+C := by
  exact Nat.add_le_add hscale hcore

/-- Exact decomposition of cyclic folding and recovery after the shared core. -/
theorem cyclic_bitSteps_eq (q B k : ℕ) (a b : Array Integer) :
    let N : ℕ := 2^k
    let scaling := scale B
    let product := convolutionCore B k scaling.value (pad q N a) (pad q N b)
    (cyclic q B k a b).bitSteps = scaling.bitSteps+product.bitSteps+
      (BinaryArrayFFT.tabulate q (fun j =>
        let folded := cellAdd (product.value.getD j.val zeroCell)
          (product.value.getD (j.val+q) zeroCell)
        let recovered := recover B scaling.value folded.value
        (⟨recovered.value, folded.bitSteps+recovered.bitSteps⟩ : BinaryResult Integer))).bitSteps := rfl

/-- Padding/precision selection changes only the array-action ledger here. -/
theorem multiplication_bitSteps_eq (q A : ℕ) (a b : Array Integer) :
    (multiplication q A a b).bitSteps =
      (cyclic q (ApproximateConvolution.convPrecision (FastConvolution.paddedExponent q) A)
        (FastConvolution.paddedExponent q) a b).bitSteps := rfl
end Actual


namespace Actual
open BinaryArrayFFT

/-- Whole stored convolution counter from the costs of its actual callbacks
and its three actual transform executions. -/
theorem convolutionCore_bitSteps_bound (B k E P Z T : ℕ)
    (s : Register ((2 ^ B : ℕ) : ℤ)) (a b : Array Integer) :
    let n : ℕ := 2^k
    let denominator := registerInput (n : ℤ)
    let leftInput := embedArray B n s a
    let rightInput := embedArray B n s b
    let left := fft B s false k leftInput.value
    let right := fft B s false k rightInput.value
    let frequencies := pointwiseArray B n s left.value right.value
    let inverse := fft B s true k frequencies.value
    (∀ i : Fin n, (embed B s (a.getD i.val zeroInteger)).bitSteps ≤ E) →
    (∀ i : Fin n, (embed B s (b.getD i.val zeroInteger)).bitSteps ≤ E) →
    left.bitSteps ≤ T → right.bitSteps ≤ T → inverse.bitSteps ≤ T →
    (∀ i : Fin n, (cellMul B s (left.value.getD i.val zeroCell)
      (right.value.getD i.val zeroCell)).bitSteps ≤ P) →
    (∀ i : Fin n, (normalize n denominator.value
      (inverse.value.getD i.val zeroCell)).bitSteps ≤ Z) →
    (convolutionCore B k s a b).bitSteps ≤
      denominator.bitSteps + 2*n*E + 3*T + n*(P+Z) := by
  dsimp only
  intro hL hR hLF hRF hIF hP hZ
  have hLE := actual_tabulate_bitSteps_bound (2^k) _ E hL
  have hRE := actual_tabulate_bitSteps_bound (2^k) _ E hR
  have hPE := actual_tabulate_bitSteps_bound (2^k) _ P hP
  have hZE := actual_tabulate_bitSteps_bound (2^k) _ Z hZ
  change (embedArray B (2^k) s a).bitSteps ≤ _ at hLE
  change (embedArray B (2^k) s b).bitSteps ≤ _ at hRE
  change (pointwiseArray B (2^k) s _ _).bitSteps ≤ _ at hPE
  change (normalizeArray (2^k) _ _).bitSteps ≤ _ at hZE
  dsimp only [convolutionCore]
  nlinarith

/-- The actual cyclic wrapper charges one shared scale, the padded core, and
one folded-plus-recovery callback for each of its `q` output coefficients. -/
theorem cyclic_bitSteps_bound (q B k C F : ℕ) (a b : Array Integer) :
    let scaling := scale B
    let product := convolutionCore B k scaling.value (pad q (2^k) a) (pad q (2^k) b)
    product.bitSteps ≤ C →
    (∀ j : Fin q,
      let folded := cellAdd (product.value.getD j.val zeroCell)
        (product.value.getD (j.val+q) zeroCell)
      folded.bitSteps + (recover B scaling.value folded.value).bitSteps ≤ F) →
    (cyclic q B k a b).bitSteps ≤ scaling.bitSteps+C+q*F := by
  dsimp only
  intro hC hF
  have hO := actual_tabulate_bitSteps_bound q (fun j =>
    let product := convolutionCore B k (scale B).value (pad q (2^k) a) (pad q (2^k) b)
    let folded := cellAdd (product.value.getD j.val zeroCell)
      (product.value.getD (j.val+q) zeroCell)
    let recovered := recover B (scale B).value folded.value
    (⟨recovered.value, folded.bitSteps+recovered.bitSteps⟩ : BinaryResult Integer)) F hF
  dsimp only [cyclic]
  nlinarith
end Actual

end ThinMatrix.BinaryArrayCosts

#print axioms ThinMatrix.BinaryArrayFFT.forward_fft_bitSteps_polynomial
#print axioms ThinMatrix.BinaryArrayFFT.inverse_fft_bitSteps_polynomial
#print axioms ThinMatrix.BinaryRootConversion.twiddle_bitSteps


namespace ThinMatrix.BinaryWholeCost
open scoped BigOperators
open FFTBitCost BinaryArrayFFT BinaryCellCost

abbrev S (k A : ℕ) : ℕ := k+A.log2+100
abbrev B (k A : ℕ) : ℕ := ApproximateConvolution.convPrecision k A
abbrev W (k A : ℕ) : ℕ := FixedPointComplex.storedBits (B k A) (2^(3*k)*A^2+2)
abbrev U (k A : ℕ) : ℕ := 2305843009213693952*(S k A)^10

theorem storedBits_mono (B : ℕ) {x y : ℕ} (h : x ≤ y) :
    FixedPointComplex.storedBits B x ≤ FixedPointComplex.storedBits B y := by
  have hlog : x.log2 ≤ y.log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right h
  simp only [FixedPointComplex.storedBits]
  omega

theorem cellFits_mono {V W : ℕ} {c : FixedPointComplex.Cell}
    (h : FixedPointComplex.CellFits V c) (hle : V ≤ W) :
    FixedPointComplex.CellFits W c :=
  ⟨fits_mono h.1 hle, fits_mono h.2 hle⟩

theorem input_fits {A : ℕ} {z : ℤ} (h : z.natAbs ≤ A) :
    BinaryCellCost.FP.Fits (A.log2+1) z := h.trans_lt Nat.lt_log2_self

theorem input_norm {A : ℕ} {z : ℤ} (h : z.natAbs ≤ A) :
    ‖(z:ℂ)‖ ≤ (A:ℝ) := by
  rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
  exact_mod_cast h

theorem W_le (k A : ℕ) : W k A ≤ 8*S k A := by
  have hW := stage_storedBits_plus_two_linear (B k A) k A
  have hB := ApproximateConvolution.convPrecision_linear k A
  dsimp [W,B,S] at *
  omega

theorem B_le (k A : ℕ) : B k A ≤ 5*S k A := by
  have hB := ApproximateConvolution.convPrecision_linear k A
  dsimp [B,S] at *
  omega

theorem W_ge (k A : ℕ) : B k A+1 ≤ W k A := by
  simp only [W,FixedPointComplex.storedBits]
  omega

theorem k_le_B (k A : ℕ) : k ≤ B k A := by
  simp only [B,ApproximateConvolution.convPrecision]
  omega

theorem primitive_envelope (k A : ℕ) : 1048576*(S k A)^3 ≤ U k A := by
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hpow : (S k A)^3 ≤ (S k A)^10 := Nat.pow_le_pow_right hS (by decide)
  dsimp [U]
  calc
    _ ≤ 1048576*(S k A)^10 := Nat.mul_le_mul_left _ hpow
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem square_envelope (k A : ℕ) : 1048576*(S k A)^2 ≤ U k A := by
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS (show 2≤3 by decide))).trans
    (primitive_envelope k A)

theorem scale_price (k A : ℕ) : (scale (B k A)).bitSteps ≤ U k A := by
  have h := scale_bitSteps (B k A)
  have hb := B_le k A
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have h1 : B k A+1 ≤ 6*S k A := by omega
  have h3 : B k A+3 ≤ 8*S k A := by omega
  apply (h.trans ?_).trans (primitive_envelope k A)
  calc
    2048*(B k A+1)*(B k A+3)^2 ≤ 2048*(6*S k A)*(8*S k A)^2 := by gcongr
    _ ≤ 1048576*(S k A)^3 := by ring_nf; omega

theorem embed_price (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ)) (a : Integer)
    (ha : a.view.natAbs ≤ A) : (embed (B k A) s a).bitSteps ≤ U k A := by
  have h := embed_bitSteps s a (input_fits ha)
  have hb := B_le k A
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hm : max (A.log2+1) (B k A+1)+2 ≤ 8*S k A := by dsimp [S] at *; omega
  apply (h.trans ?_).trans (square_envelope k A)
  calc
    256*(max (A.log2+1) (B k A+1)+2)^2+2 ≤ 256*(8*S k A)^2+2 := by gcongr
    _ ≤ 1048576*(S k A)^2 := by nlinarith

theorem pointwise_price (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ)) (a b : Cell)
    (ha : FixedPointComplex.CellFits (W k A) a.view)
    (hb : FixedPointComplex.CellFits (W k A) b.view) :
    (cellMul (B k A) s a b).bitSteps ≤ U k A := by
  have h := cellMul_bitSteps s a b ha hb
  have hw := W_le k A
  have hb := B_le k A
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hm : max (2*W k A+1) (B k A+1)+2 ≤ 20*S k A := by omega
  apply (h.trans ?_).trans (square_envelope k A)
  calc
    2048*(max (2*W k A+1) (B k A+1)+2)^2 ≤ 2048*(20*S k A)^2 := by gcongr
    _ ≤ 1048576*(S k A)^2 := by ring_nf; omega

theorem normalize_price (k A : ℕ) (d : Register ((2^k:ℕ):ℤ)) (a : Cell)
    (ha : FixedPointComplex.CellFits (W k A) a.view) :
    (normalize (2^k) d a).bitSteps ≤ U k A := by
  have hN : BinaryCellCost.FP.Fits (W k A) ((2^k:ℕ):ℤ) := by
    apply fits_mono (W:=k+1)
    · simpa [FixedPointComplex.scaleZ] using FixedPointComplex.scale_bits k
    · have := W_ge k A
      have := k_le_B k A
      omega
  have h := normalize_bitSteps d a ha hN
  have hw := W_le k A
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hm : W k A+2 ≤ 10*S k A := by omega
  apply (h.trans ?_).trans (square_envelope k A)
  calc
    512*(W k A+2)^2 ≤ 512*(10*S k A)^2 := by gcongr
    _ ≤ 1048576*(S k A)^2 := by ring_nf; omega

theorem folded_price (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ)) (a b : Cell)
    (ha : FixedPointComplex.CellFits (W k A) a.view)
    (hb : FixedPointComplex.CellFits (W k A) b.view) :
    (cellAdd a b).bitSteps + (recover (B k A) s (cellAdd a b).value).bitSteps ≤ U k A := by
  have hAdd := cellAdd_bitSteps a b ha hb
  have hFold : FixedPointComplex.CellFits (W k A+1) (cellAdd a b).value.view := by
    rw [cellAdd_view]
    exact ApproximateConvolution.add_cell_bits _ _ _ ha hb
  have hRec := recover_bitSteps s (cellAdd a b).value hFold
  have hw := W_le k A
  have hb := B_le k A
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hm : max (W k A+1) (B k A+1)+4 ≤ 13*S k A := by omega
  have hm' : W k A+2 ≤ 10*S k A := by omega
  apply (Nat.add_le_add hAdd hRec).trans
  apply (show 512*(W k A+2)^2+2048*(max (W k A+1) (B k A+1)+4)^2 ≤
      1048576*(S k A)^2 from ?_).trans (square_envelope k A)
  calc
    _ ≤ 512*(10*S k A)^2+2048*(13*S k A)^2 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem denominator_price (k A : ℕ) : (registerInput ((2^k:ℕ):ℤ)).bitSteps ≤ U k A := by
  have hN : BinaryCellCost.FP.Fits (k+1) ((2^k:ℕ):ℤ) := by
    simpa [FixedPointComplex.scaleZ] using FixedPointComplex.scale_bits k
  have h := register_input_cost hN
  have hS : 1 ≤ S k A := by dsimp [S]; omega
  have hk : k+3 ≤ S k A := by dsimp [S]; omega
  have hp : S k A ≤ (S k A)^2 := by simpa using Nat.pow_le_pow_right hS (show 1≤2 by decide)
  exact h.trans (hk.trans ((hp.trans (Nat.le_mul_of_pos_left _ (by decide))).trans (square_envelope k A)))


theorem actual_forward_fits (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ))
    (a : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, (a.getD i zeroInteger).view.natAbs ≤ A)
    (j : ℕ) (hj : j < 2^k) :
    FixedPointComplex.CellFits (W k A)
      ((fft (B k A) s false k (embedArray (B k A) (2^k) s a).value).value.getD j zeroCell).view := by
  rw [fft_getD_view_eq (B k A) k s false _
    (fun i => ApproximateConvolution.embed (B k A) (a.getD i zeroInteger).view)
    (by intro i hi; rw [embedArray, tabulate_getD _ _ i hi, embed_view])]
  have hn := fun i hi => input_norm (ha i hi)
  have h := ApproximateConvolution.forward_subcall_bits k A k 0 0
    (fun i => (a.getD i zeroInteger).view) hA (by omega) (by norm_num) hn j hj
  simp only [pow_zero,one_mul,add_zero] at h
  apply cellFits_mono h
  apply storedBits_mono
  have hp : (2:ℕ)^k ≤ 2^(3*k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hAA : A ≤ A^2 := by nlinarith
  have hm := Nat.mul_le_mul hp hAA
  omega

theorem actual_inverse_fits (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ))
    (a b : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, (a.getD i zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i < 2^k, (b.getD i zeroInteger).view.natAbs ≤ A)
    (j : ℕ) (hj : j < 2^k) :
    let frequencies := pointwiseArray (B k A) (2^k) s
      (fft (B k A) s false k (embedArray (B k A) (2^k) s a).value).value
      (fft (B k A) s false k (embedArray (B k A) (2^k) s b).value).value
    FixedPointComplex.CellFits (W k A)
      ((fft (B k A) s true k frequencies.value).value.getD j zeroCell).view := by
  dsimp only
  rw [fft_getD_view_eq (B k A) k s true _
    (fun i => (ApproximateConvolution.frequencyCells (B k A) k
      (fun t => (a.getD t zeroInteger).view) (fun t => (b.getD t zeroInteger).view)).getD i
      ApproximateConvolution.zero)
    (fun i hi => actual_frequencies_view (B k A) k s a b i hi)]
  have h := ApproximateConvolution.inverse_subcall_bits k A k 0 0
    (fun i => (a.getD i zeroInteger).view) (fun i => (b.getD i zeroInteger).view)
    hA (by omega) (by norm_num) (fun i hi => input_norm (ha i hi))
    (fun i hi => input_norm (hb i hi)) j hj
  have hp : (2:ℕ)^k*(2^(2*k)*A^2)=2^(3*k)*A^2 := by
    rw [← mul_assoc, ← pow_add, show k+2*k=3*k by omega]
  simp only [pow_zero,one_mul,add_zero,hp] at h
  exact cellFits_mono h (storedBits_mono _ (by omega))

theorem actual_core_fits (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ))
    (a b : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, (a.getD i zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i < 2^k, (b.getD i zeroInteger).view.natAbs ≤ A)
    (j : ℕ) (hj : j < 2^k) :
    FixedPointComplex.CellFits (W k A)
      ((convolutionCore (B k A) k s a b).value.getD j zeroCell).view := by
  rw [← viewCells_getD, convolutionCore_view, ArrayFFT.convolution_getD]
  have h := ApproximateConvolution.normalized_convolution_bits k A
    (fun i => (a.getD i zeroInteger).view) (fun i => (b.getD i zeroInteger).view)
    hA (fun i hi => input_norm (ha i hi)) (fun i hi => input_norm (hb i hi)) j hj
  simp only [viewIntegers_getD] at *
  exact cellFits_mono h (storedBits_mono _ (by omega))

theorem core_bitSteps (k A : ℕ) (s : Register ((2^(B k A):ℕ):ℤ))
    (a b : Array Integer) (hA : 1 ≤ A)
    (ha : ∀ i < 2^k, (a.getD i zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i < 2^k, (b.getD i zeroInteger).view.natAbs ≤ A) :
    (convolutionCore (B k A) k s a b).bitSteps ≤
      (1+(4+3*k)*2^k)*U k A := by
  have hnA := fun i hi => input_norm (ha i hi)
  have hnB := fun i hi => input_norm (hb i hi)
  have hLF := forward_fft_bitSteps_polynomial k A s a hA hnA
  have hRF := forward_fft_bitSteps_polynomial k A s b hA hnB
  have hIF := inverse_fft_bitSteps_polynomial k A s a b hA hnA hnB
  have hLE := tabulate_bitSteps_le_scratch (2^k) (U k A)
    (fun i => embed (B k A) s (a.getD i.val zeroInteger))
    (fun i => embed_price k A s _ (ha i.val i.isLt))
  have hRE := tabulate_bitSteps_le_scratch (2^k) (U k A)
    (fun i => embed (B k A) s (b.getD i.val zeroInteger))
    (fun i => embed_price k A s _ (hb i.val i.isLt))
  have hPE := tabulate_bitSteps_le_scratch (2^k) (U k A)
    (fun i => cellMul (B k A) s
      ((fft (B k A) s false k (embedArray (B k A) (2^k) s a).value).value.getD i.val zeroCell)
      ((fft (B k A) s false k (embedArray (B k A) (2^k) s b).value).value.getD i.val zeroCell))
    (fun i => pointwise_price k A s _ _
      (actual_forward_fits k A s a hA ha i.val i.isLt)
      (actual_forward_fits k A s b hA hb i.val i.isLt))
  have hZE := tabulate_bitSteps_le_scratch (2^k) (U k A)
    (fun i => normalize (2^k) (registerInput ((2^k:ℕ):ℤ)).value
      ((fft (B k A) s true k (pointwiseArray (B k A) (2^k) s
        (fft (B k A) s false k (embedArray (B k A) (2^k) s a).value).value
        (fft (B k A) s false k (embedArray (B k A) (2^k) s b).value).value).value).value.getD i.val zeroCell))
    (fun i => normalize_price k A _ _ (actual_inverse_fits k A s a b hA ha hb i.val i.isLt))
  have hD := denominator_price k A
  change (embedArray (B k A) (2^k) s a).bitSteps ≤ _ at hLE
  change (embedArray (B k A) (2^k) s b).bitSteps ≤ _ at hRE
  change (pointwiseArray (B k A) (2^k) s _ _).bitSteps ≤ _ at hPE
  change (normalizeArray (2^k) _ _).bitSteps ≤ _ at hZE
  dsimp only [convolutionCore]
  calc
    _ ≤ U k A+2^k*U k A+2^k*U k A+k*2^k*U k A+k*2^k*U k A+
        2^k*U k A+k*2^k*U k A+2^k*U k A := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hD hLE) hRE) hLF) hRF) hPE) hIF) hZE
    _ = _ := by ring


theorem pad_bound (q N A : ℕ) (a : Array Integer)
    (ha : ∀ i < q, (a.getD i zeroInteger).view.natAbs ≤ A) :
    ∀ i < N, ((pad q N a).getD i zeroInteger).view.natAbs ≤ A := by
  intro i hi
  rw [pad,ArrayFFT.getD_ofFn _ i hi]
  split
  · exact ha i ‹i<q›
  · simp

theorem cyclic_bitSteps_uniform (q k A : ℕ) (a b : Array Integer)
    (hA : 1 ≤ A) (hN : 2*q ≤ 2^k)
    (ha : ∀ i < q, (a.getD i zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i < q, (b.getD i zeroInteger).view.natAbs ≤ A) :
    (cyclic q (B k A) k a b).bitSteps ≤ 7*(k+1)*2^k*U k A := by
  have hpa := pad_bound q (2^k) A a ha
  have hpb := pad_bound q (2^k) A b hb
  let s := (scale (B k A)).value
  let product := convolutionCore (B k A) k s (pad q (2^k) a) (pad q (2^k) b)
  have hcore := core_bitSteps k A s _ _ hA hpa hpb
  have hout := tabulate_bitSteps_le_scratch q (U k A) (fun j =>
    let folded := cellAdd (product.value.getD j.val zeroCell)
      (product.value.getD (j.val+q) zeroCell)
    let recovered := recover (B k A) s folded.value
    (⟨recovered.value,folded.bitSteps+recovered.bitSteps⟩ : BinaryResult Integer)) (by
      intro j
      have hj : j.val < 2^k := by have := j.isLt; omega
      have hjq : j.val+q < 2^k := by have := j.isLt; omega
      exact folded_price k A s _ _
        (actual_core_fits k A s _ _ hA hpa hpb j.val hj)
        (actual_core_fits k A s _ _ hA hpa hpb (j.val+q) hjq))
  have hs := scale_price k A
  have hlen : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by decide)
  have hq : q ≤ 2^k := by omega
  have hcount : 2+(4+3*k)*2^k+q ≤ 7*(k+1)*2^k := by
    calc
      _ ≤ 2*2^k+(4+3*k)*2^k+2^k := by omega
      _ = (7+3*k)*2^k := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  change (scale (B k A)).bitSteps+product.bitSteps+_ ≤ _
  calc
    _ ≤ U k A+(1+(4+3*k)*2^k)*U k A+q*U k A :=
      Nat.add_le_add (Nat.add_le_add hs hcore) hout
    _ = (2+(4+3*k)*2^k+q)*U k A := by ring
    _ ≤ 7*(k+1)*2^k*U k A := Nat.mul_le_mul_right _ hcount

/-- Unconditional full cyclic circuit bound at the certified convolution
precision. Inputs are already stored binary integers; array control has its
separate `arrayActions` ledger. -/
theorem cyclic_bitSteps_polynomial (q k A : ℕ) (a b : Array Integer)
    (hA : 1 ≤ A) (hN : 2*q ≤ 2^k)
    (ha : ∀ i < q, (a.getD i zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i < q, (b.getD i zeroInteger).view.natAbs ≤ A) :
    (cyclic q (B k A) k a b).bitSteps ≤
      18446744073709551616*(k+1)*2^k*(S k A)^10 := by
  calc
    _ ≤ 7*(k+1)*2^k*U k A := cyclic_bitSteps_uniform q k A a b hA hN ha hb
    _ = 16140901064495857664*(k+1)*2^k*(S k A)^10 := by dsimp only [U]; ring
    _ ≤ _ := by gcongr; norm_num

/-- The actual multiplication wrapper has near-linear binary circuit work
up to a fixed polynomial in the logarithmic dimensions and input magnitude. -/
theorem multiplication_bitSteps_polynomial (q A : ℕ) [NeZero q] (a b : Array Integer)
    (hA : 1 ≤ A)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) :
    let k := FastConvolution.paddedExponent q
    (multiplication q A a b).bitSteps ≤
      73786976294838206464*(k+1)*q*(S k A)^10 := by
  let k := FastConvolution.paddedExponent q
  have hN := FastConvolution.padded_length_bounds q (NeZero.pos q)
  have h := cyclic_bitSteps_polynomial q k A a b hA hN.1
    (fun i hi => ha ⟨i,hi⟩) (fun i hi => hb ⟨i,hi⟩)
  change (cyclic q (B k A) k a b).bitSteps ≤ _
  calc
    _ ≤ 18446744073709551616*(k+1)*2^k*(S k A)^10 := h
    _ ≤ 18446744073709551616*(k+1)*(4*q)*(S k A)^10 := by
      gcongr
      exact hN.2
    _ = _ := by ring

/-- Expanded logarithmic version of the preceding actual program bound. -/
theorem multiplication_bitSteps_polylog (q A : ℕ) [NeZero q] (a b : Array Integer)
    (hA : 1 ≤ A)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) :
    (multiplication q A a b).bitSteps ≤
      73786976294838206464*(q.log2+3)*q*(q.log2+A.log2+102)^10 := by
  have h := multiplication_bitSteps_polynomial q A a b hA ha hb
  convert h using 1
  dsimp only [FastConvolution.paddedExponent,S]
  congr 2
  omega

end ThinMatrix.BinaryWholeCost

namespace ThinMatrix.BinaryArrayFFT

theorem multiplication_bitSteps_bound (q A : ℕ) [NeZero q] (a b : Array Integer)
    (hA : 1 ≤ A)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) :
    (multiplication q A a b).bitSteps ≤
      73786976294838206464*(q.log2+3)*q*(q.log2+A.log2+102)^10 :=
  BinaryWholeCost.multiplication_bitSteps_polylog q A a b hA ha hb

theorem multiplication_totalSteps_bound (q A : ℕ) [NeZero q] (a b : Array Integer)
    (hA : 1 ≤ A)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) :
    (multiplication q A a b).bitSteps + (multiplication q A a b).arrayActions ≤
      147573952589676412928*(q.log2+3)*q*(q.log2+A.log2+102)^10 := by
  let S := q.log2+A.log2+102
  have hbits := multiplication_bitSteps_bound q A a b hA ha hb
  have harr := multiplication_arrayActions q A a b
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S^2 ≤ S^10 := Nat.pow_le_pow_right hS (by decide)
  have harr' : (multiplication q A a b).arrayActions ≤ 8192*(q.log2+3)*q*S^10 := by
    have harr'' : (multiplication q A a b).arrayActions ≤ 8192*(q.log2+3)*q*S^2 := by
      convert harr using 1
      dsimp only [FastConvolution.paddedExponent, S]
      congr 2; omega
    exact harr''.trans (Nat.mul_le_mul_left _ hp)
  change _ + _ ≤ 147573952589676412928*(q.log2+3)*q*S^10
  calc
    _ ≤ 73786976294838206464*(q.log2+3)*q*S^10 + 8192*(q.log2+3)*q*S^10 := Nat.add_le_add hbits harr'
    _ = (73786976294838206464+8192)*(q.log2+3)*q*S^10 := by ring
    _ ≤ _ := by gcongr; norm_num

theorem multiplication_correct_and_cost (q A : ℕ) [NeZero q] (hA : 1 ≤ A) (a b : Array Integer)
    (ha : ∀ i : Fin q, (a.getD i.val zeroInteger).view.natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val zeroInteger).view.natAbs ≤ A) :
    (∀ j : Fin q, ((multiplication q A a b).value.getD j.val zeroInteger).view =
      CyclicRing.convolution (ArrayFFT.asCyclic q (viewIntegers a)) (ArrayFFT.asCyclic q (viewIntegers b)) j) ∧
    (multiplication q A a b).bitSteps + (multiplication q A a b).arrayActions ≤
      147573952589676412928*(q.log2+3)*q*(q.log2+A.log2+102)^10 :=
  ⟨multiplication_correct q A hA a b ha hb, multiplication_totalSteps_bound q A a b hA ha hb⟩

#print axioms multiplication_bitSteps_bound
#print axioms multiplication_totalSteps_bound
#print axioms multiplication_correct_and_cost
end ThinMatrix.BinaryArrayFFT
