import ApproximateConvolution

/-!
# Finite-array implementation of the integer-cell FFT

The primitive finite-array-cell model charges one bounds test and one read
for each Array.getD, and one action per write. Tabulation allocates once and
charges one write and two loop
control actions per cell; its callback reads and index arithmetic are charged
separately. Integer-cell and rational-root arithmetic use the already proved
arithmetic allowance. Root synthesis is a charged subroutine backed by its
integer-arithmetic ledger; its internal control is outside this array ledger.
The two power-of-two lengths are formed once per node, with their index work
in the conservative node allowance. This is an explicit array cost model, not a refinement
to the separate instruction-level word RAM.

The executable transform uses Array.getD and materializes both children and
the twiddle table once. List access appears only in the specification proofs.
-/

namespace ThinMatrix.ArrayFFT

abbrev Cell := FixedPointComplex.Cell

def tabulationActions (n reads indices : ℕ) : ℕ := 1 + n * (2 * reads + indices + 3)

def nodeArrayActions (k : ℕ) : ℕ :=
  tabulationActions (2 ^ k) 1 1 + tabulationActions (2 ^ k) 1 2 +
    tabulationActions (2 ^ (k + 1)) 0 0 +
    tabulationActions (2 ^ (k + 1)) 3 1 + 4 * k + 16

structure Result (α : Type) where
  value : Array α
  arithmeticAllowance : ℕ
  arrayActions : ℕ

def fft (B : ℕ) (inverse : Bool) : ℕ → Array Cell → Result Cell
  | 0, a => ⟨#[a.getD 0 ApproximateConvolution.zero], 0, 8⟩
  | k + 1, a =>
      let half := 2 ^ k
      let full := 2 ^ (k + 1)
      let evenInput := Array.ofFn (fun i : Fin half => a.getD (2 * i.val) ApproximateConvolution.zero)
      let oddInput := Array.ofFn (fun i : Fin half => a.getD (2 * i.val + 1) ApproximateConvolution.zero)
      let even := fft B inverse k evenInput
      let odd := fft B inverse k oddInput
      let twiddles := Array.ofFn (fun j : Fin full =>
        ApproximateConvolution.twiddle B (k + 1) inverse j.val)
      let output := Array.ofFn (fun j : Fin full =>
        let index := j.val % half
        FixedPointComplex.add (even.value.getD index ApproximateConvolution.zero)
          (FixedPointComplex.mul B (twiddles.getD j.val ApproximateConvolution.zero)
            (odd.value.getD index ApproximateConvolution.zero)))
      ⟨output, even.arithmeticAllowance + odd.arithmeticAllowance +
        full * ApproximateConvolution.fftUnitCost B,
        even.arrayActions + odd.arrayActions + nodeArrayActions k⟩

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem getD_toList {α : Type} (a : Array α) (i : ℕ) (d : α) :
    a.toList.getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem fft_size (B k : ℕ) (inverse : Bool) (a : Array Cell) :
    (fft B inverse k a).value.size = 2 ^ k := by
  cases k <;> simp [fft]

theorem fft_getD_succ (B k : ℕ) (inverse : Bool) (a : Array Cell) (j : ℕ)
    (hj : j < 2 ^ (k + 1)) :
    (fft B inverse (k + 1) a).value.getD j ApproximateConvolution.zero =
      FixedPointComplex.add
        ((fft B inverse k (Array.ofFn (fun i : Fin (2 ^ k) =>
          a.getD (2 * i.val) ApproximateConvolution.zero))).value.getD (j % 2 ^ k) ApproximateConvolution.zero)
        (FixedPointComplex.mul B (ApproximateConvolution.twiddle B (k + 1) inverse j)
          ((fft B inverse k (Array.ofFn (fun i : Fin (2 ^ k) =>
            a.getD (2 * i.val + 1) ApproximateConvolution.zero))).value.getD (j % 2 ^ k) ApproximateConvolution.zero)) := by
  simp only [fft]
  rw [getD_ofFn _ j hj, getD_ofFn _ j hj]

theorem fft_toList_eq (B k : ℕ) (inverse : Bool) (a : Array Cell) (x : ℕ → Cell)
    (ha : ∀ i < 2 ^ k, a.getD i ApproximateConvolution.zero = x i) :
    (fft B inverse k a).value.toList = (ApproximateConvolution.fft B inverse k x).value := by
  induction k generalizing a x with
  | zero =>
      have h := ha 0 (by norm_num)
      simpa [fft, ApproximateConvolution.fft] using congrArg (fun c => [c]) h
  | succ k ih =>
      have he := ih
        (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val) ApproximateConvolution.zero))
        (fun i => x (2 * i)) (by
          intro i hi
          rw [getD_ofFn _ i hi]
          exact ha _ (by rw [pow_succ]; omega))
      have ho := ih
        (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val + 1) ApproximateConvolution.zero))
        (fun i => x (2 * i + 1)) (by
          intro i hi
          rw [getD_ofFn _ i hi]
          exact ha _ (by rw [pow_succ]; omega))
      apply List.ext_getElem
      · simp [fft_size, ApproximateConvolution.fft_length]
      · intro j hj₁ hj₂
        have hj : j < 2 ^ (k + 1) := by simpa [fft_size] using hj₁
        rw [← List.getD_eq_getElem _ ApproximateConvolution.zero hj₁,
          ← List.getD_eq_getElem _ ApproximateConvolution.zero hj₂,
          getD_toList, fft_getD_succ B k inverse a j hj,
          ApproximateConvolution.fft_getD_succ B k inverse x j hj]
        rw [← getD_toList, he, ← getD_toList, ho]

theorem fft_toList (B k : ℕ) (inverse : Bool) (a : Array Cell) :
    (fft B inverse k a).value.toList =
      (ApproximateConvolution.fft B inverse k (fun i => a.getD i ApproximateConvolution.zero)).value :=
  fft_toList_eq B k inverse a _ (by intros; rfl)

theorem fft_arithmeticAllowance (B k : ℕ) (inverse : Bool) (a : Array Cell) :
    (fft B inverse k a).arithmeticAllowance = k * 2 ^ k * ApproximateConvolution.fftUnitCost B := by
  induction k generalizing a with
  | zero => simp [fft]
  | succ k ih =>
      simp only [fft, ih]
      rw [pow_succ]
      ring

theorem depth_le_length (k : ℕ) : k + 1 ≤ (2 : ℕ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; nlinarith


theorem nodeArrayActions_le (k : ℕ) : nodeArrayActions k ≤ 32 * 2 ^ (k + 1) := by
  unfold nodeArrayActions tabulationActions
  rw [pow_succ]
  have hp := depth_le_length k
  omega

theorem fft_arrayActions (B k : ℕ) (inverse : Bool) (a : Array Cell) :
    (fft B inverse k a).arrayActions ≤ 32 * (k + 1) * 2 ^ k := by
  induction k generalizing a with
  | zero => simp [fft]
  | succ k ih =>
      have he := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val) ApproximateConvolution.zero))
      have ho := ih (Array.ofFn (fun i : Fin (2 ^ k) => a.getD (2 * i.val + 1) ApproximateConvolution.zero))
      have hn := nodeArrayActions_le k
      simp only [fft]
      rw [pow_succ] at hn ⊢
      nlinarith


theorem tabulate_toList {α : Type} (n : ℕ) (f : ℕ → α) :
    (Array.ofFn (fun i : Fin n => f i.val)).toList = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

def embedArray (B N : ℕ) (a : Array ℤ) : Array Cell :=
  Array.ofFn (fun i : Fin N => ApproximateConvolution.embed B (a.getD i.val 0))

def pointwiseArray (B N : ℕ) (a b : Array Cell) : Array Cell :=
  Array.ofFn (fun i : Fin N => FixedPointComplex.mul B
    (a.getD i.val ApproximateConvolution.zero) (b.getD i.val ApproximateConvolution.zero))

def normalizeArray (N : ℕ) (a : Array Cell) : Array Cell :=
  Array.ofFn (fun i : Fin N => ApproximateConvolution.normalize N (a.getD i.val ApproximateConvolution.zero))

theorem pointwiseArray_toList (B N : ℕ) (a b : Array Cell) :
    (pointwiseArray B N a b).toList =
      (ApproximateConvolution.pointwise B N a.toList b.toList).value := by
  simpa only [pointwiseArray, ApproximateConvolution.pointwise,
    FastConvolution.Counted.sequence_value, getD_toList] using
      tabulate_toList N (fun i => FixedPointComplex.mul B
        (a.getD i ApproximateConvolution.zero) (b.getD i ApproximateConvolution.zero))

theorem normalizeArray_toList (N : ℕ) (a : Array Cell) :
    (normalizeArray N a).toList = (ApproximateConvolution.normalizeVector N a.toList).value := by
  simpa only [normalizeArray, ApproximateConvolution.normalizeVector,
    FastConvolution.Counted.sequence_value, getD_toList] using
      tabulate_toList N (fun i => ApproximateConvolution.normalize N (a.getD i ApproximateConvolution.zero))

def convolution (B k : ℕ) (a b : Array ℤ) : Result Cell :=
  let N := 2 ^ k
  let left := fft B false k (embedArray B N a)
  let right := fft B false k (embedArray B N b)
  let frequencies := pointwiseArray B N left.value right.value
  let inverse := fft B true k frequencies
  let output := normalizeArray N inverse.value
  ⟨output, left.arithmeticAllowance + right.arithmeticAllowance + inverse.arithmeticAllowance +
    (4 * B + 14) * N,
    left.arrayActions + right.arrayActions + inverse.arrayActions +
      2 * tabulationActions N 1 0 + tabulationActions N 2 0 + tabulationActions N 1 0 + 4 * k + 16⟩

theorem convolution_toList_eq (B k : ℕ) (a b : Array ℤ) (x y : ℕ → ℤ)
    (ha : ∀ i < 2 ^ k, a.getD i 0 = x i) (hb : ∀ i < 2 ^ k, b.getD i 0 = y i) :
    (convolution B k a b).value.toList =
      (ApproximateConvolution.convolution B k x y).value := by
  let N := 2 ^ k
  let left := fft B false k (embedArray B N a)
  let right := fft B false k (embedArray B N b)
  let frequencies := pointwiseArray B N left.value right.value
  let inverse := fft B true k frequencies
  let listLeft := ApproximateConvolution.fft B false k (fun i => ApproximateConvolution.embed B (x i))
  let listRight := ApproximateConvolution.fft B false k (fun i => ApproximateConvolution.embed B (y i))
  let listFrequencies := ApproximateConvolution.pointwise B N listLeft.value listRight.value
  have hl : left.value.toList = listLeft.value := fft_toList_eq B k false _ _ (by
    intro i hi
    rw [embedArray, getD_ofFn _ i hi, ha i hi])
  have hr : right.value.toList = listRight.value := fft_toList_eq B k false _ _ (by
    intro i hi
    rw [embedArray, getD_ofFn _ i hi, hb i hi])
  have hf : frequencies.toList = listFrequencies.value := by
    dsimp only [frequencies, listFrequencies]
    rw [pointwiseArray_toList, hl, hr]
  have hi : inverse.value.toList =
      (ApproximateConvolution.fft B true k (fun i => listFrequencies.value.getD i ApproximateConvolution.zero)).value :=
    fft_toList_eq B k true frequencies _ (by
      intro i hi
      rw [← getD_toList, hf])
  change (normalizeArray N inverse.value).toList =
    (ApproximateConvolution.normalizeVector N
      (ApproximateConvolution.fft B true k (fun i => listFrequencies.value.getD i ApproximateConvolution.zero)).value).value
  rw [normalizeArray_toList, hi]

theorem convolution_toList (B k : ℕ) (a b : Array ℤ) :
    (convolution B k a b).value.toList =
      (ApproximateConvolution.convolution B k (fun i => a.getD i 0) (fun i => b.getD i 0)).value :=
  convolution_toList_eq B k a b _ _ (by intros; rfl) (by intros; rfl)


theorem convolution_size (B k : ℕ) (a b : Array ℤ) : (convolution B k a b).value.size = 2 ^ k := by
  simp [convolution, normalizeArray]

theorem convolution_arithmeticAllowance (B k : ℕ) (a b : Array ℤ) :
    (convolution B k a b).arithmeticAllowance =
      3 * k * 2 ^ k * ApproximateConvolution.fftUnitCost B + (4 * B + 14) * 2 ^ k := by
  simp only [convolution, fft_arithmeticAllowance]
  ring

theorem convolution_arrayActions (B k : ℕ) (a b : Array ℤ) :
    (convolution B k a b).arrayActions ≤ 160 * (k + 1) * 2 ^ k := by
  let N := 2 ^ k
  have hl := fft_arrayActions B k false (embedArray B N a)
  have hr := fft_arrayActions B k false (embedArray B N b)
  have hi := fft_arrayActions B k true (pointwiseArray B N
    (fft B false k (embedArray B N a)).value (fft B false k (embedArray B N b)).value)
  have hN : 1 ≤ N := by dsimp [N]; exact one_le_pow₀ (by norm_num)
  have hk : k + 1 ≤ N := depth_le_length k
  change _ + _ + _ + 2 * tabulationActions N 1 0 + tabulationActions N 2 0 + tabulationActions N 1 0 + 4 * k + 16 ≤ _
  unfold tabulationActions
  dsimp [N] at *
  nlinarith



def asCyclic (q : ℕ) (a : Array ℤ) : CyclicRing.Cyclic q := fun i => a.getD i.val 0

def pad (q N : ℕ) (a : Array ℤ) : Array ℤ :=
  Array.ofFn (fun i : Fin N => if i.val < q then a.getD i.val 0 else 0)

theorem pad_getD (q N : ℕ) (a : Array ℤ) (i : ℕ) (hi : i < N) :
    (pad q N a).getD i 0 = ApproximateConvolution.zeroPadInt (asCyclic q a) i := by
  rw [pad, getD_ofFn _ i hi]
  unfold ApproximateConvolution.zeroPadInt asCyclic
  split <;> rfl

def cyclic (q B k : ℕ) (a b : Array ℤ) : Result ℤ :=
  let N := 2 ^ k
  let product := convolution B k (pad q N a) (pad q N b)
  let output := Array.ofFn (fun j : Fin q => FixedPointComplex.recover B (FixedPointComplex.add
    (product.value.getD j.val ApproximateConvolution.zero)
    (product.value.getD (j.val + q) ApproximateConvolution.zero)))
  ⟨output, product.arithmeticAllowance + (8 * B + 32) * q,
    product.arrayActions + 2 * tabulationActions N 1 1 + tabulationActions q 2 1 + 4 * k + 16⟩

theorem cyclic_toList (q B k : ℕ) (a b : Array ℤ) :
    (cyclic q B k a b).value.toList =
      (ApproximateConvolution.cyclic B k (asCyclic q a) (asCyclic q b)).value := by
  let N := 2 ^ k
  let product := convolution B k (pad q N a) (pad q N b)
  have hp : product.value.toList =
      (ApproximateConvolution.convolution B k
        (ApproximateConvolution.zeroPadInt (asCyclic q a))
        (ApproximateConvolution.zeroPadInt (asCyclic q b))).value :=
    convolution_toList_eq B k _ _ _ _ (fun i hi => pad_getD q N a i hi) (fun i hi => pad_getD q N b i hi)
  have ht := tabulate_toList q (fun j => FixedPointComplex.recover B (FixedPointComplex.add
    (product.value.getD j ApproximateConvolution.zero) (product.value.getD (j + q) ApproximateConvolution.zero)))
  change (Array.ofFn (fun j : Fin q => FixedPointComplex.recover B (FixedPointComplex.add
    (product.value.getD j.val ApproximateConvolution.zero)
    (product.value.getD (j.val + q) ApproximateConvolution.zero)))).toList =
      (FastConvolution.Counted.sequence (fun j =>
        ⟨FixedPointComplex.recover B (FixedPointComplex.add
          ((ApproximateConvolution.convolution B k
            (ApproximateConvolution.zeroPadInt (asCyclic q a))
            (ApproximateConvolution.zeroPadInt (asCyclic q b))).value.getD j ApproximateConvolution.zero)
          ((ApproximateConvolution.convolution B k
            (ApproximateConvolution.zeroPadInt (asCyclic q a))
            (ApproximateConvolution.zeroPadInt (asCyclic q b))).value.getD (j + q) ApproximateConvolution.zero)), 8 * B + 32⟩)
        (List.range q)).value
  rw [FastConvolution.Counted.sequence_value, ht]
  apply List.map_congr_left
  intro j hj
  rw [← getD_toList, hp, ← getD_toList, hp]

theorem cyclic_size (q B k : ℕ) (a b : Array ℤ) : (cyclic q B k a b).value.size = q := by
  simp [cyclic]

theorem cyclic_arithmeticAllowance (q B k : ℕ) (a b : Array ℤ) :
    (cyclic q B k a b).arithmeticAllowance =
      3 * k * 2 ^ k * ApproximateConvolution.fftUnitCost B + (4 * B + 14) * 2 ^ k + (8 * B + 32) * q := by
  simp only [cyclic, convolution_arithmeticAllowance]

theorem cyclic_arrayActions (q B k : ℕ) (a b : Array ℤ) (hN : 2 * q ≤ 2 ^ k) :
    (cyclic q B k a b).arrayActions ≤ 224 * (k + 1) * 2 ^ k := by
  have hc := convolution_arrayActions B k (pad q (2 ^ k) a) (pad q (2 ^ k) b)
  have hp : 1 ≤ (2 : ℕ) ^ k := one_le_pow₀ (by norm_num)
  have hk := depth_le_length k
  change _ + 2 * tabulationActions (2 ^ k) 1 1 + tabulationActions q 2 1 + 4 * k + 16 ≤ _
  unfold tabulationActions
  nlinarith

def multiplication (q A : ℕ) (a b : Array ℤ) : Result ℤ :=
  let k := FastConvolution.paddedExponent q
  cyclic q (ApproximateConvolution.convPrecision k A) k a b

theorem multiplication_toList (q A : ℕ) (a b : Array ℤ) :
    (multiplication q A a b).value.toList =
      (ApproximateConvolution.multiplication A (asCyclic q a) (asCyclic q b)).value :=
  cyclic_toList q _ _ a b

theorem multiplication_getD (q A : ℕ) (a b : Array ℤ) (j : ℕ) :
    (multiplication q A a b).value.getD j 0 =
      (ApproximateConvolution.multiplication A (asCyclic q a) (asCyclic q b)).value.getD j 0 := by
  rw [← getD_toList, multiplication_toList]

theorem multiplication_correct (q A : ℕ) [NeZero q] (hA : 1 ≤ A) (a b : Array ℤ)
    (ha : ∀ i : Fin q, ‖(a.getD i.val 0 : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i : Fin q, ‖(b.getD i.val 0 : ℂ)‖ ≤ (A : ℝ)) (j : Fin q) :
    (multiplication q A a b).value.getD j.val 0 = CyclicRing.convolution (asCyclic q a) (asCyclic q b) j := by
  rw [multiplication_getD]
  exact ApproximateConvolution.multiplication_correct A hA _ _ ha hb j

theorem multiplication_arrayActions (q A : ℕ) [NeZero q] (a b : Array ℤ) :
    let k := FastConvolution.paddedExponent q
    (multiplication q A a b).arrayActions ≤ 896 * (k + 1) * q := by
  let k := FastConvolution.paddedExponent q
  have hN := FastConvolution.padded_length_bounds q (NeZero.pos q)
  have hc := cyclic_arrayActions q (ApproximateConvolution.convPrecision k A) k a b hN.1
  change (multiplication q A a b).arrayActions ≤ _
  calc
    _ ≤ 224 * (k + 1) * 2 ^ k := hc
    _ ≤ 224 * (k + 1) * (4 * q) := Nat.mul_le_mul_left _ hN.2
    _ = _ := by ring



theorem root_output_arithmetic_le (B k j : ℕ) :
    (RationalWorkBounds.rootC (2 ^ (k + 1)) j B).operations + 8 * B + 64 ≤
      ApproximateConvolution.fftUnitCost B := by
  exact Nat.add_le_add_right (Nat.add_le_add_right (RationalWorkBounds.rootC_operations _ _ _) _) _

theorem fft_list_operations_le_allowance (B k : ℕ) (inverse : Bool) (a : Array Cell) :
    (ApproximateConvolution.fft B inverse k (fun i => a.getD i ApproximateConvolution.zero)).operations ≤
      (fft B inverse k a).arithmeticAllowance := by
  rw [fft_arithmeticAllowance]
  exact ApproximateConvolution.fft_operations _ _ _ _

theorem convolution_list_operations_le_allowance (B k : ℕ) (a b : Array ℤ) :
    (ApproximateConvolution.convolution B k (fun i => a.getD i 0) (fun i => b.getD i 0)).operations ≤
      (convolution B k a b).arithmeticAllowance := by
  rw [convolution_arithmeticAllowance]
  exact ApproximateConvolution.convolution_operations _ _ _ _

theorem cyclic_list_operations_le_allowance (q B k : ℕ) (a b : Array ℤ) :
    (ApproximateConvolution.cyclic B k (asCyclic q a) (asCyclic q b)).operations ≤
      (cyclic q B k a b).arithmeticAllowance := by
  rw [cyclic_arithmeticAllowance]
  exact ApproximateConvolution.cyclic_operations _ _ _ _

theorem multiplication_list_operations_le_allowance (q A : ℕ) (a b : Array ℤ) :
    (ApproximateConvolution.multiplication A (asCyclic q a) (asCyclic q b)).operations ≤
      (multiplication q A a b).arithmeticAllowance :=
  cyclic_list_operations_le_allowance q _ _ a b

theorem fft_getD (B k : ℕ) (inverse : Bool) (a : Array Cell) (j : ℕ) :
    (fft B inverse k a).value.getD j ApproximateConvolution.zero =
      (ApproximateConvolution.fft B inverse k (fun i => a.getD i ApproximateConvolution.zero)).value.getD j ApproximateConvolution.zero := by
  rw [← getD_toList, fft_toList]

theorem convolution_getD (B k : ℕ) (a b : Array ℤ) (j : ℕ) :
    (convolution B k a b).value.getD j ApproximateConvolution.zero =
      (ApproximateConvolution.convolution B k (fun i => a.getD i 0) (fun i => b.getD i 0)).value.getD j ApproximateConvolution.zero := by
  rw [← getD_toList, convolution_toList]

theorem cyclic_getD (q B k : ℕ) (a b : Array ℤ) (j : ℕ) :
    (cyclic q B k a b).value.getD j 0 =
      (ApproximateConvolution.cyclic B k (asCyclic q a) (asCyclic q b)).value.getD j 0 := by
  rw [← getD_toList, cyclic_toList]

theorem multiplication_correct_natAbs (q A : ℕ) [NeZero q] (hA : 1 ≤ A) (a b : Array ℤ)
    (ha : ∀ i : Fin q, (a.getD i.val 0).natAbs ≤ A)
    (hb : ∀ i : Fin q, (b.getD i.val 0).natAbs ≤ A) (j : Fin q) :
    (multiplication q A a b).value.getD j.val 0 = CyclicRing.convolution (asCyclic q a) (asCyclic q b) j := by
  rw [multiplication_getD]
  exact ApproximateConvolution.multiplication_correct_natAbs A hA _ _ ha hb j

theorem multiplication_size (q A : ℕ) (a b : Array ℤ) : (multiplication q A a b).value.size = q :=
  cyclic_size q _ _ a b

theorem multiplication_arithmeticAllowance_polynomial (q A : ℕ) [NeZero q] (a b : Array ℤ) :
    let k := FastConvolution.paddedExponent q
    let B := ApproximateConvolution.convPrecision k A
    (multiplication q A a b).arithmeticAllowance ≤
      12 * k * q * (100 * (B + k + 78) ^ 2 + 8 * B + 64) + (24 * B + 88) * q := by
  let k := FastConvolution.paddedExponent q
  let B := ApproximateConvolution.convPrecision k A
  have hN := (FastConvolution.padded_length_bounds q (NeZero.pos q)).2
  have hR := RationalWorkBounds.rootOperations_polynomial B k
  have hC : ApproximateConvolution.fftUnitCost B ≤ 100 * (B + k + 78) ^ 2 + 8 * B + 64 := by
    unfold ApproximateConvolution.fftUnitCost
    omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left (3 * k) hN) hC
  have hadd := Nat.mul_le_mul_left (4 * B + 14) hN
  change (cyclic q B k a b).arithmeticAllowance ≤ _
  rw [cyclic_arithmeticAllowance]
  nlinarith

theorem multiplication_arithmeticAllowance_logarithmic (q A : ℕ) [NeZero q] (a b : Array ℤ) :
    let k := FastConvolution.paddedExponent q
    (multiplication q A a b).arithmeticAllowance ≤
      45000 * (k + 1) * q * (k + A.log2 + 100) ^ 2 := by
  let k := FastConvolution.paddedExponent q
  let B := ApproximateConvolution.convPrecision k A
  let S := k + A.log2 + 100
  have hc := multiplication_arithmeticAllowance_polynomial q A a b
  change (multiplication q A a b).arithmeticAllowance ≤ _
  have hB : B ≤ 5 * S := by have := ApproximateConvolution.convPrecision_linear k A; dsimp [B, S]; omega
  have hT : B + k + 78 ≤ 6 * S := by have := ApproximateConvolution.convPrecision_linear k A; dsimp [B, S]; omega
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hSq : (B + k + 78) ^ 2 ≤ (6 * S) ^ 2 := by gcongr
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hC : 100 * (B + k + 78) ^ 2 + 8 * B + 64 ≤ 3704 * S ^ 2 := by nlinarith
  have hTail : 24 * B + 88 ≤ 208 * S ^ 2 := by nlinarith
  calc
    _ ≤ 12 * k * q * (100 * (B + k + 78) ^ 2 + 8 * B + 64) + (24 * B + 88) * q := hc
    _ ≤ 12 * k * q * (3704 * S ^ 2) + (208 * S ^ 2) * q := by gcongr
    _ = (44448 * k + 208) * (q * S ^ 2) := by ring
    _ ≤ (45000 * (k + 1)) * (q * S ^ 2) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem multiplication_totalAllowance (q A : ℕ) [NeZero q] (a b : Array ℤ) :
    let k := FastConvolution.paddedExponent q
    (multiplication q A a b).arithmeticAllowance + (multiplication q A a b).arrayActions ≤
      46000 * (k + 1) * q * (k + A.log2 + 100) ^ 2 := by
  let k := FastConvolution.paddedExponent q
  let S := k + A.log2 + 100
  have ha := multiplication_arithmeticAllowance_logarithmic q A a b
  have hm := multiplication_arrayActions q A a b
  have hS : 1 ≤ S ^ 2 := one_le_pow₀ (show 1 ≤ S by dsimp [S]; omega)
  have hscale := Nat.mul_le_mul_left ((k + 1) * q) hS
  change _ + _ ≤ _
  dsimp [k, S] at *
  nlinarith


#print axioms fft_toList
#print axioms fft_arithmeticAllowance
#print axioms fft_arrayActions
#print axioms convolution_toList
#print axioms convolution_arrayActions
#print axioms multiplication_correct
#print axioms multiplication_arrayActions
#print axioms root_output_arithmetic_le
#print axioms fft_list_operations_le_allowance
#print axioms multiplication_list_operations_le_allowance
#print axioms multiplication_correct_natAbs
#print axioms multiplication_arithmeticAllowance_logarithmic
#print axioms multiplication_totalAllowance

end ThinMatrix.ArrayFFT
