import FastConvolution
import FixedPointComplex
import RootsApproximation
import RationalWorkBounds

/-!
# Integer-cell Fourier arithmetic

All executable values are integer cells or unreduced rational root data.
Complex numbers occur only in the specification and error proofs. The
arithmetic allowance includes integer additions, multiplications, divisions
and scale construction. Array access and control have their own finite-array
ledger in `ArrayFFT`.
-/

namespace ThinMatrix.ApproximateConvolution

open scoped BigOperators

def zero : FixedPointComplex.Cell := ⟨0, 0⟩
def conjugate (c : FixedPointComplex.Cell) : FixedPointComplex.Cell := ⟨c.re, -c.im⟩

/-- Integer-only conversion of a shared-denominator raw rational cell. -/
def ofRaw (B : ℕ) (r : RationalWorkBounds.Raw) : FixedPointComplex.Cell :=
  ⟨r.re * FixedPointComplex.scaleZ B / (r.den : ℤ), r.im * FixedPointComplex.scaleZ B / (r.den : ℤ)⟩

theorem ofRaw_eq_ofRat (B : ℕ) (r : RationalWorkBounds.Raw) (hr : RationalWorkBounds.Valid r) :
    ofRaw B r = FixedPointComplex.ofRat B (RationalWorkBounds.value r) := by
  have hd : (0 : ℤ) < r.den := by exact_mod_cast hr
  apply FixedPointComplex.Cell.ext <;> simp only [ofRaw, FixedPointComplex.ofRat, RationalWorkBounds.value]
  · rw [← FixedPointComplex.floor_rat_cast, ← FixedPointComplex.floor_int_div _ _ hd]
    congr 1
    push_cast
    simp only [FixedPointComplex.scaleZ]
    push_cast
    ring
  · rw [← FixedPointComplex.floor_rat_cast, ← FixedPointComplex.floor_int_div _ _ hd]
    congr 1
    push_cast
    simp only [FixedPointComplex.scaleZ]
    push_cast
    ring

theorem rational_cast_eq (z : ℚ × ℚ) : FixedPointComplex.ratComplex z = RootsApproximation.ratComplex z := by
  apply Complex.ext <;> simp [FixedPointComplex.ratComplex, RootsApproximation.ratComplex]

theorem decode_conjugate (B : ℕ) (c : FixedPointComplex.Cell) :
    FixedPointComplex.decode B (conjugate c) = star (FixedPointComplex.decode B c) := by
  apply Complex.ext <;> simp [FixedPointComplex.decode, conjugate, neg_div]

noncomputable def omega (k : ℕ) (inverse : Bool) : ℂ :=
  if inverse then (FastConvolution.complexRoot k)⁻¹ else FastConvolution.complexRoot k

theorem omega_norm (k : ℕ) (inverse : Bool) : ‖omega k inverse‖ = 1 := by
  have h : ‖FastConvolution.complexRoot k‖ = 1 := by
    simp [FastConvolution.complexRoot, ZMod.stdAddChar_apply]
  cases inverse <;> simp [omega, h]

theorem omega_square (k : ℕ) (inverse : Bool) :
    omega (k + 1) inverse ^ 2 = omega k inverse := by
  have h : FastConvolution.complexRoot (k + 1) ^ 2 = FastConvolution.complexRoot k := by
    have hp (n : ℕ) : FastConvolution.complexRoot n =
        Complex.exp (Complex.I * ((2 * Real.pi / (2 ^ n : ℝ) : ℝ) : ℂ)) := by
      have hphase := RootsApproximation.stdAddChar_phase (2 ^ n) 1
      simpa only [FastConvolution.complexRoot, Nat.cast_one, mul_one, Nat.cast_pow,
        Nat.cast_ofNat] using hphase
    rw [hp, hp]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  cases inverse <;> simp [omega, inv_pow, h]

/-- Every twiddle is synthesized from the proved integer root evaluator. -/
def twiddle (B k : ℕ) (inverse : Bool) (j : ℕ) : FixedPointComplex.Cell :=
  let r := (RationalWorkBounds.rootC (2 ^ k) j B).result
  let c := ofRaw B r
  if inverse then conjugate c else c

theorem twiddle_error (B k : ℕ) (inverse : Bool) (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B (twiddle B k inverse j) - omega k inverse ^ j‖ ≤ 2 * FixedPointComplex.eps B := by
  have hc := RationalWorkBounds.rootC_certificate (B := B) (L := k) (by positivity : 0 < 2 ^ k)
    (le_refl (2 ^ k)) hj
  have he := RootsApproximation.rootApprox_stdAddChar_error (2 ^ k) j B hj
  have hrat : ‖FixedPointComplex.ratComplex (RationalWorkBounds.value (RationalWorkBounds.rootC (2 ^ k) j B).result) -
      FastConvolution.complexRoot k ^ j‖ ≤ 1 / FixedPointComplex.scale B := by
    rw [rational_cast_eq, hc.1, FastConvolution.complexRoot_power]
    exact he
  have hcell := FixedPointComplex.rational_twiddle_error B
    (RationalWorkBounds.value (RationalWorkBounds.rootC (2 ^ k) j B).result) (FastConvolution.complexRoot k ^ j) hrat
  rw [← ofRaw_eq_ofRat _ _ hc.2.1] at hcell
  cases inverse with
  | false => simpa [twiddle, omega] using hcell
  | true =>
    have hu : ‖FastConvolution.complexRoot k ^ j‖ = 1 := by
      rw [norm_pow]
      have h := omega_norm k false
      simpa [omega] using congrArg (fun r : ℝ => r ^ j) h
    have hi : (FastConvolution.complexRoot k)⁻¹ ^ j = star (FastConvolution.complexRoot k ^ j) := by
      rw [inv_pow, Complex.inv_eq_conj hu]
      rfl
    simp only [twiddle, ↓reduceIte, omega, hi, decode_conjugate]
    rw [← star_sub, norm_star]
    exact hcell

/-- Finite, memoized integer-cell FFT. Child arrays are computed once;
each output uses one rounded multiplication and one exact addition. -/
def fft (B : ℕ) (inverse : Bool) : ℕ → (ℕ → FixedPointComplex.Cell) → FastConvolution.Counted (List FixedPointComplex.Cell)
  | 0, a => ⟨[a 0], 0⟩
  | k + 1, a =>
    let even := fft B inverse k (fun i => a (2 * i))
    let odd := fft B inverse k (fun i => a (2 * i + 1))
    let output := FastConvolution.Counted.sequence (fun j =>
      ⟨FixedPointComplex.add (even.value.getD (j % 2 ^ k) zero)
        (FixedPointComplex.mul B (twiddle B (k + 1) inverse j)
          (odd.value.getD (j % 2 ^ k) zero)),
        (RationalWorkBounds.rootC (2 ^ (k + 1)) j B).operations + 8 * B + 64⟩)
      (List.range (2 ^ (k + 1)))
    ⟨output.value, even.operations + odd.operations + output.operations⟩

theorem fft_length (B k : ℕ) (inverse : Bool) (a : ℕ → FixedPointComplex.Cell) :
    (fft B inverse k a).value.length = 2 ^ k := by
  cases k with
  | zero => rfl
  | succ k => simp [fft, FastConvolution.Counted.sequence_value]

theorem fft_getD_succ (B k : ℕ) (inverse : Bool) (a : ℕ → FixedPointComplex.Cell)
    (j : ℕ) (hj : j < 2 ^ (k + 1)) :
    (fft B inverse (k + 1) a).value.getD j zero =
      FixedPointComplex.add ((fft B inverse k (fun i => a (2 * i))).value.getD (j % 2 ^ k) zero)
        (FixedPointComplex.mul B (twiddle B (k + 1) inverse j)
          ((fft B inverse k (fun i => a (2 * i + 1))).value.getD (j % 2 ^ k) zero)) := by
  simp only [fft, FastConvolution.Counted.sequence_value]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]

theorem radixFFT_norm (k : ℕ) (w : ℂ) (a : ℕ → ℂ) (A : ℝ)
    (hA : 0 ≤ A) (hw : ‖w‖ ≤ 1) (ha : ∀ i < 2 ^ k, ‖a i‖ ≤ A) (j : ℕ) :
    ‖FastConvolution.radixFFT k w a j‖ ≤ (2 : ℝ) ^ k * A := by
  induction k generalizing w a j with
  | zero => simpa [FastConvolution.radixFFT] using ha 0 (by norm_num)
  | succ k ih =>
    have hs : ‖w ^ 2‖ ≤ 1 := by simpa [norm_pow] using pow_le_one₀ (norm_nonneg w) hw (n := 2)
    have hei (i : ℕ) (hi : i < 2 ^ k) : 2 * i < 2 ^ (k + 1) := by
      rw [pow_succ]; omega
    have hoi (i : ℕ) (hi : i < 2 ^ k) : 2 * i + 1 < 2 ^ (k + 1) := by
      rw [pow_succ]; omega
    have he := ih (w ^ 2) (fun i => a (2 * i)) hs
      (fun i hi => ha (2 * i) (hei i hi))
      (j % 2 ^ k)
    have ho := ih (w ^ 2) (fun i => a (2 * i + 1)) hs
      (fun i hi => ha (2 * i + 1) (hoi i hi))
      (j % 2 ^ k)
    have hpw : ‖w ^ j‖ ≤ 1 := by simpa [norm_pow] using pow_le_one₀ (norm_nonneg w) hw (n := j)
    simp only [FastConvolution.radixFFT]
    calc
      _ ≤ ‖FastConvolution.radixFFT k (w ^ 2) (fun i => a (2 * i)) (j % 2 ^ k)‖ +
          ‖w ^ j * FastConvolution.radixFFT k (w ^ 2) (fun i => a (2 * i + 1)) (j % 2 ^ k)‖ := norm_add_le _ _
      _ ≤ (2 : ℝ) ^ k * A + (2 : ℝ) ^ k * A := by
        rw [norm_mul]
        exact add_le_add he ((mul_le_mul_of_nonneg_left ho (norm_nonneg _)).trans
          (by simpa using mul_le_mul_of_nonneg_right hpw (by positivity : 0 ≤ (2 : ℝ) ^ k * A)))
      _ = _ := by rw [pow_succ]; ring

noncomputable def fftError (B k : ℕ) (A E : ℝ) : ℝ :=
  (4 : ℝ) ^ (k + 1) * (E + (A + 1) * FixedPointComplex.eps B)

theorem fft_error (B k : ℕ) (inverse : Bool) (a : ℕ → FixedPointComplex.Cell) (x : ℕ → ℂ)
    (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖x i‖ ≤ A)
    (hx : ∀ i < 2 ^ k, ‖FixedPointComplex.decode B (a i) - x i‖ ≤ E)
    (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((fft B inverse k a).value.getD j zero) -
      FastConvolution.radixFFT k (omega k inverse) x j‖ ≤ fftError B k A E := by
  induction k generalizing a x j with
  | zero =>
    have hj₀ : j = 0 := by simpa using hj
    subst j
    have h := hx 0 (by norm_num)
    simp only [fft, List.getD_cons_zero, FastConvolution.radixFFT]
    apply h.trans
    unfold fftError
    have hp := (FixedPointComplex.eps_pos B).le
    norm_num
    nlinarith
  | succ k ih =>
    have hm : j % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have hei (i : ℕ) (hi : i < 2 ^ k) : 2 * i < 2 ^ (k + 1) := by
      rw [pow_succ]; omega
    have hoi (i : ℕ) (hi : i < 2 ^ k) : 2 * i + 1 < 2 ^ (k + 1) := by
      rw [pow_succ]; omega
    have he := ih (fun i => a (2 * i)) (fun i => x (2 * i))
      (fun i hi => ha _ (hei i hi)) (fun i hi => hx _ (hei i hi)) _ hm
    have ho := ih (fun i => a (2 * i + 1)) (fun i => x (2 * i + 1))
      (fun i hi => ha _ (hoi i hi)) (fun i hi => hx _ (hoi i hi)) _ hm
    have hn := radixFFT_norm k (omega k inverse) (fun i => x (2 * i + 1)) A hA
      (omega_norm _ _).le (fun i hi => ha _ (hoi i hi)) (j % 2 ^ k)
    have hsize : ‖FixedPointComplex.decode B
        ((fft B inverse k (fun i => a (2 * i + 1))).value.getD (j % 2 ^ k) zero)‖ ≤
        fftError B k A E + (2 : ℝ) ^ k * A := by
      exact (norm_le_norm_sub_add _ _).trans (add_le_add ho hn)
    have hunit : ‖omega (k + 1) inverse ^ j‖ ≤ 1 := by
      rw [norm_pow, omega_norm]; simp
    have hb := (FixedPointComplex.butterfly_stage B
      ((fft B inverse k (fun i => a (2 * i))).value.getD (j % 2 ^ k) zero)
      ((fft B inverse k (fun i => a (2 * i + 1))).value.getD (j % 2 ^ k) zero)
      (twiddle B (k + 1) inverse j)
      (FastConvolution.radixFFT k (omega k inverse) (fun i => x (2 * i)) (j % 2 ^ k))
      (FastConvolution.radixFFT k (omega k inverse) (fun i => x (2 * i + 1)) (j % 2 ^ k))
      (omega (k + 1) inverse ^ j) (fftError B k A E)
      (fftError B k A E + (2 : ℝ) ^ k * A) 2 (by norm_num)
      he ho (twiddle_error B (k + 1) inverse j hj) hunit hsize).1
    rw [fft_getD_succ B k inverse a j hj]
    simp only [FastConvolution.radixFFT, omega_square]
    apply hb.trans
    have hp := (FixedPointComplex.eps_pos B).le
    have hec : 0 ≤ fftError B k A E := by
      unfold fftError
      exact mul_nonneg (by positivity) (add_nonneg hE (mul_nonneg (by linarith) hp))
    have hecsmall := mul_le_mul_of_nonneg_right heps hec
    have hpower : (2 : ℝ) * 2 ^ k ≤ 4 ^ (k + 1) := by
      rw [mul_comm, ← pow_succ]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hone : (1 : ℝ) ≤ 4 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hextra : (2 * (2 : ℝ) ^ k * A + 1) * FixedPointComplex.eps B ≤ fftError B k A E := by
      have h₁ : 2 * (2 : ℝ) ^ k * A + 1 ≤ 4 ^ (k + 1) * (A + 1) := by
        nlinarith [mul_le_mul_of_nonneg_right hpower hA]
      have h₂ := mul_le_mul_of_nonneg_right h₁ hp
      unfold fftError
      nlinarith [mul_nonneg (by positivity : 0 ≤ (4 : ℝ) ^ (k + 1)) hE]
    have hnext : fftError B (k + 1) A E = 4 * fftError B k A E := by
      unfold fftError
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [hnext]
    nlinarith

theorem sequence_operations_le {α β : Type*} (f : α → FastConvolution.Counted β) (xs : List α)
    (C : ℕ) (h : ∀ x ∈ xs, (f x).operations ≤ C) :
    (FastConvolution.Counted.sequence f xs).operations ≤ C * xs.length := by
  induction xs with
  | nil => simp [FastConvolution.Counted.sequence]
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [FastConvolution.Counted.sequence, List.length_cons]
    nlinarith

def fftUnitCost (B : ℕ) : ℕ := RationalWorkBounds.rootOperations B + 8 * B + 64

theorem fft_operations (B k : ℕ) (inverse : Bool) (a : ℕ → FixedPointComplex.Cell) :
    (fft B inverse k a).operations ≤ k * 2 ^ k * fftUnitCost B := by
  induction k generalizing a with
  | zero => simp [fft]
  | succ k ih =>
    have he := ih (fun i => a (2 * i))
    have ho := ih (fun i => a (2 * i + 1))
    have hs := sequence_operations_le (fun j =>
      (⟨FixedPointComplex.add ((fft B inverse k (fun i => a (2 * i))).value.getD (j % 2 ^ k) zero)
        (FixedPointComplex.mul B (twiddle B (k + 1) inverse j)
          ((fft B inverse k (fun i => a (2 * i + 1))).value.getD (j % 2 ^ k) zero)),
        (RationalWorkBounds.rootC (2 ^ (k + 1)) j B).operations + 8 * B + 64⟩ : FastConvolution.Counted FixedPointComplex.Cell))
      (List.range (2 ^ (k + 1))) (fftUnitCost B) (by
        intro j hj
        exact Nat.add_le_add_right (Nat.add_le_add_right (RationalWorkBounds.rootC_operations _ _ _) _) _)
    simp only [List.length_range] at hs
    simp only [fft]
    rw [pow_succ] at hs ⊢
    nlinarith

def embed (B : ℕ) (z : ℤ) : FixedPointComplex.Cell :=
  ⟨z * FixedPointComplex.scaleZ B, 0⟩

theorem decode_embed (B : ℕ) (z : ℤ) : FixedPointComplex.decode B (embed B z) = (z : ℂ) := by
  apply Complex.ext <;> simp [embed, FixedPointComplex.decode,
    ne_of_gt (FixedPointComplex.scale_pos B)]

def normalize (N : ℕ) (c : FixedPointComplex.Cell) : FixedPointComplex.Cell :=
  ⟨c.re / (N : ℤ), c.im / (N : ℤ)⟩

theorem normalize_eq_quantize (B N : ℕ) (hN : 0 < N) (c : FixedPointComplex.Cell) :
    normalize N c = FixedPointComplex.quantize B (FixedPointComplex.decode B c / (N : ℂ)) := by
  have hd : (0 : ℤ) < N := by exact_mod_cast hN
  apply FixedPointComplex.Cell.ext
  · change c.re / (N : ℤ) = ⌊(FixedPointComplex.decode B c / (N : ℂ)).re * FixedPointComplex.scale B⌋
    rw [← FixedPointComplex.floor_int_div _ _ hd]
    congr 1
    simp [FixedPointComplex.decode]
    field_simp [ne_of_gt (FixedPointComplex.scale_pos B)]
  · change c.im / (N : ℤ) = ⌊(FixedPointComplex.decode B c / (N : ℂ)).im * FixedPointComplex.scale B⌋
    rw [← FixedPointComplex.floor_int_div _ _ hd]
    congr 1
    simp [FixedPointComplex.decode]
    field_simp [ne_of_gt (FixedPointComplex.scale_pos B)]

theorem normalize_error (B N : ℕ) (hN : 0 < N) (c : FixedPointComplex.Cell)
    (z : ℂ) (E : ℝ) (h : ‖FixedPointComplex.decode B c - z‖ ≤ E) :
    ‖FixedPointComplex.decode B (normalize N c) - z / (N : ℂ)‖ ≤
      FixedPointComplex.eps B + E / (N : ℝ) := by
  rw [normalize_eq_quantize B N hN c]
  have hdiv : ‖FixedPointComplex.decode B c / (N : ℂ) - z / (N : ℂ)‖ ≤ E / (N : ℝ) := by
    rw [← sub_div, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right h (by positivity)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (FixedPointComplex.decode B c / (N : ℂ)) _).trans
    (add_le_add (FixedPointComplex.quantize_error B _) hdiv)

def pointwise (B N : ℕ) (a b : List FixedPointComplex.Cell) :
    FastConvolution.Counted (List FixedPointComplex.Cell) :=
  FastConvolution.Counted.sequence (fun j =>
    ⟨FixedPointComplex.mul B (a.getD j zero) (b.getD j zero), 2 * B + 8⟩) (List.range N)

theorem pointwise_getD (B N : ℕ) (a b : List FixedPointComplex.Cell) (j : ℕ) (hj : j < N) :
    (pointwise B N a b).value.getD j zero =
      FixedPointComplex.mul B (a.getD j zero) (b.getD j zero) := by
  rw [pointwise, FastConvolution.Counted.sequence_value]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]

def normalizeVector (N : ℕ) (a : List FixedPointComplex.Cell) :
    FastConvolution.Counted (List FixedPointComplex.Cell) :=
  FastConvolution.Counted.sequence (fun j => ⟨normalize N (a.getD j zero), 2⟩) (List.range N)

theorem normalizeVector_getD (N : ℕ) (a : List FixedPointComplex.Cell) (j : ℕ) (hj : j < N) :
    (normalizeVector N a).value.getD j zero = normalize N (a.getD j zero) := by
  rw [normalizeVector, FastConvolution.Counted.sequence_value]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]

/-- Entire rounded ordinary-convolution program, with integer inputs. -/
def convolution (B k : ℕ) (a b : ℕ → ℤ) : FastConvolution.Counted (List FixedPointComplex.Cell) :=
  let left := fft B false k (fun i => embed B (a i))
  let right := fft B false k (fun i => embed B (b i))
  let frequencies := pointwise B (2 ^ k) left.value right.value
  let inverse := fft B true k (fun i => frequencies.value.getD i zero)
  let output := normalizeVector (2 ^ k) inverse.value
  ⟨output.value, left.operations + right.operations + frequencies.operations +
    inverse.operations + output.operations + 2 * 2 ^ k * (B + 2)⟩

noncomputable def forwardError (B k : ℕ) (A : ℝ) : ℝ := fftError B k A 0
noncomputable def frequencyError (B k : ℕ) (A : ℝ) : ℝ :=
  FixedPointComplex.eps B + forwardError B k A *
    ((2 : ℝ) ^ k * A + forwardError B k A) + (2 : ℝ) ^ k * A * forwardError B k A
noncomputable def convolutionError (B k : ℕ) (A : ℝ) : ℝ :=
  FixedPointComplex.eps B + fftError B k ((2 : ℝ) ^ (2 * k) * A ^ 2)
    (frequencyError B k A) / (2 : ℝ) ^ k

theorem radixFFT_congr (k : ℕ) (w : ℂ) (a b : ℕ → ℂ)
    (hw : w ^ (2 ^ k) = 1) (h : ∀ i < 2 ^ k, a i = b i) (j : ℕ) :
    FastConvolution.radixFFT k w a j = FastConvolution.radixFFT k w b j := by
  rw [FastConvolution.radixFFT_eq_polynomialDFT k w a hw,
    FastConvolution.radixFFT_eq_polynomialDFT k w b hw]
  unfold FastConvolution.polynomialDFT
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem exact_inverse_product (k : ℕ) (P Q : Polynomial ℤ)
    (hP : P.natDegree < 2 ^ k) (hQ : Q.natDegree < 2 ^ k)
    (hPQ : (P * Q).natDegree < 2 ^ k) (j : ℕ) (hj : j < 2 ^ k) :
    FastConvolution.radixFFT k (omega k true)
      (fun i => FastConvolution.radixFFT k (omega k false) (fun t => (P.coeff t : ℂ)) i *
        FastConvolution.radixFFT k (omega k false) (fun t => (Q.coeff t : ℂ)) i) j /
      (2 ^ k : ℂ) = ((P * Q).coeff j : ℂ) := by
  have h := FastConvolution.convolutionCounted_integer k P Q hP hQ hPQ j hj
  simp only [FastConvolution.convolutionCounted] at h
  rw [FastConvolution.scaleVector_getD _ _ _ j hj,
    FastConvolution.fftCounted_getD _ _ _ j hj] at h
  have hf (i : ℕ) (hi : i < 2 ^ k) :
      (FastConvolution.pointwiseProduct (2 ^ k)
        (FastConvolution.fftCounted k (FastConvolution.complexRoot k) (fun t => (P.coeff t : ℂ))).value
        (FastConvolution.fftCounted k (FastConvolution.complexRoot k) (fun t => (Q.coeff t : ℂ))).value).value.getD i 0 =
      FastConvolution.radixFFT k (FastConvolution.complexRoot k) (fun t => (P.coeff t : ℂ)) i *
        FastConvolution.radixFFT k (FastConvolution.complexRoot k) (fun t => (Q.coeff t : ℂ)) i := by
    rw [FastConvolution.pointwiseProduct_getD _ _ _ i hi,
      FastConvolution.fftCounted_getD _ _ _ i hi, FastConvolution.fftCounted_getD _ _ _ i hi]
  rw [radixFFT_congr k _ _ _ (FastConvolution.complexRoot_inv_pow k) hf j] at h
  simpa [omega, div_eq_mul_inv, mul_comm] using h

theorem forward_error (B k : ℕ) (a : ℕ → ℤ) (A : ℝ) (hA : 0 ≤ A)
    (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ A) (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((fft B false k (fun i => embed B (a i))).value.getD j zero) -
      FastConvolution.radixFFT k (omega k false) (fun i => (a i : ℂ)) j‖ ≤ forwardError B k A := by
  apply fft_error B k false _ _ A 0 hA (by norm_num) heps ha
  · intro i hi
    simp [decode_embed]
  · exact hj

theorem convolution_error (B k : ℕ) (a b : ℕ → ℤ) (A : ℝ) (hA : 0 ≤ A)
    (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ A)
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ A) (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((convolution B k a b).value.getD j zero) -
      FastConvolution.radixFFT k (omega k true)
        (fun i => FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) i *
          FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) i) j /
        (2 ^ k : ℂ)‖ ≤ convolutionError B k A := by
  let left := fft B false k (fun i => embed B (a i))
  let right := fft B false k (fun i => embed B (b i))
  let frequencies := pointwise B (2 ^ k) left.value right.value
  let f := fun i => FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) i
  let g := fun i => FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) i
  have hE : 0 ≤ forwardError B k A := by
    unfold forwardError fftError
    exact mul_nonneg (by positivity) (by have := (FixedPointComplex.eps_pos B).le; positivity)
  have hnF (i : ℕ) : ‖f i‖ ≤ (2 : ℝ) ^ k * A :=
    radixFFT_norm k _ _ A hA (omega_norm _ _).le ha i
  have hnG (i : ℕ) : ‖g i‖ ≤ (2 : ℝ) ^ k * A :=
    radixFFT_norm k _ _ A hA (omega_norm _ _).le hb i
  have hF (i : ℕ) (hi : i < 2 ^ k) :
      ‖FixedPointComplex.decode B (left.value.getD i zero) - f i‖ ≤ forwardError B k A :=
    forward_error B k a A hA heps ha i hi
  have hG (i : ℕ) (hi : i < 2 ^ k) :
      ‖FixedPointComplex.decode B (right.value.getD i zero) - g i‖ ≤ forwardError B k A :=
    forward_error B k b A hA heps hb i hi
  have hGsize (i : ℕ) (hi : i < 2 ^ k) :
      ‖FixedPointComplex.decode B (right.value.getD i zero)‖ ≤
        (2 : ℝ) ^ k * A + forwardError B k A := by
    have h := (norm_le_norm_sub_add (FixedPointComplex.decode B (right.value.getD i zero)) (g i)).trans
      (add_le_add (hG i hi) (hnG i))
    linarith
  have hp (i : ℕ) (hi : i < 2 ^ k) :
      ‖FixedPointComplex.decode B (frequencies.value.getD i zero) - f i * g i‖ ≤ frequencyError B k A := by
    change ‖FixedPointComplex.decode B ((pointwise B (2 ^ k) left.value right.value).value.getD i zero) - _‖ ≤ _
    rw [pointwise_getD _ _ _ _ i hi]
    have h := FixedPointComplex.mul_error B (left.value.getD i zero) (right.value.getD i zero)
      (f i) (g i) (forwardError B k A) (forwardError B k A) (hF i hi) (hG i hi)
    apply h.trans
    unfold frequencyError
    gcongr
    · exact hGsize i hi
    · exact hnF i
  have hfreq : 0 ≤ frequencyError B k A := by
    unfold frequencyError
    have he := (FixedPointComplex.eps_pos B).le
    positivity
  have hn (i : ℕ) (hi : i < 2 ^ k) : ‖f i * g i‖ ≤ (2 : ℝ) ^ (2 * k) * A ^ 2 := by
    rw [norm_mul]
    calc
      _ ≤ ((2 : ℝ) ^ k * A) * ((2 : ℝ) ^ k * A) :=
        mul_le_mul (hnF i) (hnG i) (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_comm 2 k, pow_mul]; ring
  have hi := fft_error B k true (fun i => frequencies.value.getD i zero) (fun i => f i * g i)
    ((2 : ℝ) ^ (2 * k) * A ^ 2) (frequencyError B k A) (by positivity) hfreq heps hn hp j hj
  change ‖FixedPointComplex.decode B
      ((normalizeVector (2 ^ k) (fft B true k (fun i => frequencies.value.getD i zero)).value).value.getD j zero) - _‖ ≤ _
  rw [normalizeVector_getD _ _ j hj]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, convolutionError] using
    normalize_error B (2 ^ k) (by positivity) _ _ _ hi

theorem convolution_integer_error (B k : ℕ) (P Q : Polynomial ℤ) (A : ℝ) (hA : 0 ≤ A)
    (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖(P.coeff i : ℂ)‖ ≤ A)
    (hb : ∀ i < 2 ^ k, ‖(Q.coeff i : ℂ)‖ ≤ A)
    (hP : P.natDegree < 2 ^ k) (hQ : Q.natDegree < 2 ^ k)
    (hPQ : (P * Q).natDegree < 2 ^ k) (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((convolution B k P.coeff Q.coeff).value.getD j zero) -
      ((P * Q).coeff j : ℂ)‖ ≤ convolutionError B k A := by
  have h := convolution_error B k P.coeff Q.coeff A hA heps ha hb j hj
  rw [exact_inverse_product k P Q hP hQ hPQ j hj] at h
  exact h



def convPrecision (k A : ℕ) : ℕ := 3 + 5 * k + (2048 * A ^ 2).log2 + 1

theorem convPrecision_two_le (k A : ℕ) : 2 ≤ convPrecision k A := by
  unfold convPrecision
  omega

theorem convPrecision_scale (k A : ℕ) :
    2048 * ((2 : ℝ) ^ k) ^ 5 * (A : ℝ) ^ 2 < FixedPointComplex.scale (convPrecision k A) := by
  have h := FixedPointComplex.scaled_magnitude_lt (3 + 5 * k) (2048 * A ^ 2)
  have hn : 2048 * A ^ 2 * 2 ^ (3 + 5 * k) < 2 ^ convPrecision k A := by
    simpa only [FixedPointComplex.storedBits, convPrecision] using h
  have hr : (2048 : ℝ) * (A : ℝ) ^ 2 * 2 ^ (3 + 5 * k) < FixedPointComplex.scale (convPrecision k A) := by
    unfold FixedPointComplex.scale
    exact_mod_cast hn
  have hp : (2 : ℝ) ^ (3 + 5 * k) = 8 * ((2 : ℝ) ^ k) ^ 5 := by
    rw [show 3 + 5 * k = 3 + k * 5 by omega, pow_add, pow_mul]
    norm_num
  rw [hp] at hr
  have hnonneg : 0 ≤ ((2 : ℝ) ^ k) ^ 5 * (A : ℝ) ^ 2 := by positivity
  nlinarith

theorem convPrecision_small (k A : ℕ) :
    512 * ((2 : ℝ) ^ k) ^ 5 * (A : ℝ) ^ 2 * FixedPointComplex.eps (convPrecision k A) < 1 / 2 := by
  have ht := convPrecision_scale k A
  have hs := FixedPointComplex.scale_pos (convPrecision k A)
  unfold FixedPointComplex.eps
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hs).mpr
  nlinarith

theorem convPrecision_eps_le (k A : ℕ) : FixedPointComplex.eps (convPrecision k A) ≤ 1 / 2 := by
  have hB := convPrecision_two_le k A
  have hp : (4 : ℝ) ≤ FixedPointComplex.scale (convPrecision k A) := by
    have hpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hB
    norm_num at hpow
    simpa [FixedPointComplex.scale] using hpow
  unfold FixedPointComplex.eps
  apply (div_le_iff₀ (FixedPointComplex.scale_pos _)).mpr
  nlinarith


theorem pipeline_forward_bound (N A e : ℝ) (hA : 1 ≤ A) (he : 0 ≤ e) :
    4 * N ^ 2 * (A + 1) * e ≤ 8 * N ^ 2 * A * e := by
  have h := mul_le_mul_of_nonneg_left (show A + 1 ≤ 2 * A by linarith)
    (show 0 ≤ 4 * N ^ 2 * e by positivity)
  nlinarith

theorem pipeline_forward_small (N A e : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A) (he : 0 ≤ e)
    (hs : 512 * N ^ 5 * A ^ 2 * e < 1 / 2) :
    8 * N ^ 2 * A * e ≤ 1 := by
  have hN25 : N ^ 2 ≤ N ^ 5 := pow_le_pow_right₀ hN (by norm_num)
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hm : N ^ 2 * A ≤ N ^ 5 * A ^ 2 :=
    mul_le_mul hN25 hA2 (by linarith) (by positivity)
  have hme := mul_le_mul_of_nonneg_right hm he
  nlinarith

theorem pipeline_pointwise_bound (N A e F : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (he : 0 ≤ e) (hF : 0 ≤ F) (hFs : F ≤ 1)
    (hFb : F ≤ 8 * N ^ 2 * A * e) :
    e + F * (N * A + F) + N * A * F ≤ 25 * N ^ 3 * A ^ 2 * e := by
  have hNA : 1 ≤ N * A := one_le_mul_of_one_le_of_one_le hN hA
  have hMon : 1 ≤ N ^ 3 * A ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ hA)
  calc
    e + F * (N * A + F) + N * A * F ≤ e + F * (N * A + 1) + N * A * F := by
      gcongr
    _ ≤ e + 3 * N * A * F := by
      nlinarith [mul_nonneg hF (sub_nonneg.mpr hNA)]
    _ ≤ e + 3 * N * A * (8 * N ^ 2 * A * e) := by
      gcongr
    _ = e + 24 * N ^ 3 * A ^ 2 * e := by ring
    _ ≤ 25 * N ^ 3 * A ^ 2 * e := by
      nlinarith [mul_le_mul_of_nonneg_right hMon he]

theorem pipeline_inverse_bound (N A e P : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (he : 0 ≤ e) (hP : P ≤ 25 * N ^ 3 * A ^ 2 * e) :
    4 * N ^ 2 * (P + (N ^ 2 * A ^ 2 + 1) * e) ≤ 108 * N ^ 5 * A ^ 2 * e := by
  have hN23 : N ^ 2 ≤ N ^ 3 := pow_le_pow_right₀ hN (by norm_num)
  have hN3A2 : 1 ≤ N ^ 3 * A ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ hA)
  have hmid : N ^ 2 * A ^ 2 + 1 ≤ 2 * N ^ 3 * A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hN23 (sq_nonneg A)
    linarith
  calc
    _ ≤ 4 * N ^ 2 * (25 * N ^ 3 * A ^ 2 * e + (2 * N ^ 3 * A ^ 2) * e) := by
      gcongr
    _ = _ := by ring

theorem pipeline_fold_bound (N A e I : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (he : 0 ≤ e) (hI : I ≤ 108 * N ^ 5 * A ^ 2 * e) :
    2 * (e + I / N) ≤ 218 * N ^ 4 * A ^ 2 * e := by
  have hNp : 0 < N := by linarith
  have hmon : 1 ≤ N ^ 4 * A ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ hA)
  have hd : I / N ≤ 108 * N ^ 4 * A ^ 2 * e := by
    apply (div_le_iff₀ hNp).mpr
    nlinarith [hI]
  nlinarith [mul_le_mul_of_nonneg_right hmon he]

theorem pipeline_fold_small (N A e I : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (he : 0 ≤ e) (hI : I ≤ 108 * N ^ 5 * A ^ 2 * e)
    (hs : 512 * N ^ 5 * A ^ 2 * e < 1 / 2) :
    2 * (e + I / N) < 1 / 2 := by
  have hb := pipeline_fold_bound N A e I hN hA he hI
  have hN45 : N ^ 4 ≤ N ^ 5 := pow_le_pow_right₀ hN (by norm_num)
  have hm : 218 * N ^ 4 * A ^ 2 * e ≤ 512 * N ^ 5 * A ^ 2 * e := by
    have h := mul_le_mul_of_nonneg_right hN45 (show 0 ≤ A ^ 2 * e by positivity)
    nlinarith [mul_nonneg (show 0 ≤ N ^ 5 by positivity) (show 0 ≤ A ^ 2 * e by positivity)]
  exact hb.trans_lt (hm.trans_lt hs)



theorem four_pow_fft_length (k : ℕ) :
    (4 : ℝ) ^ (k + 1) = 4 * ((2 : ℝ) ^ k) ^ 2 := by
  rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 k, pow_mul]
  ring

theorem pipeline_complete_small (N A e : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (he : 0 ≤ e) (hs : 512 * N ^ 5 * A ^ 2 * e < 1 / 2) :
    let F := 4 * N ^ 2 * (A + 1) * e
    let P := e + F * (N * A + F) + (N * A) * F
    let I := 4 * N ^ 2 * (P + (N ^ 2 * A ^ 2 + 1) * e)
    2 * (e + I / N) < 1 / 2 := by
  let F := 4 * N ^ 2 * (A + 1) * e
  let P := e + F * (N * A + F) + (N * A) * F
  let I := 4 * N ^ 2 * (P + (N ^ 2 * A ^ 2 + 1) * e)
  change 2 * (e + I / N) < 1 / 2
  have hFb : F ≤ 8 * N ^ 2 * A * e := pipeline_forward_bound N A e hA he
  have hFs : F ≤ 1 := hFb.trans (pipeline_forward_small N A e hN hA he hs)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : P ≤ 25 * N ^ 3 * A ^ 2 * e := pipeline_pointwise_bound N A e F hN hA he hF hFs hFb
  have hI : I ≤ 108 * N ^ 5 * A ^ 2 * e := pipeline_inverse_bound N A e P hN hA he hP
  exact pipeline_fold_small N A e I hN hA he hI hs



theorem convolutionError_small (k A : ℕ) (hA : 1 ≤ A) :
    2 * convolutionError (convPrecision k A) k (A : ℝ) < 1 / 2 := by
  have h := pipeline_complete_small ((2 : ℝ) ^ k) (A : ℝ)
    (FixedPointComplex.eps (convPrecision k A)) (one_le_pow₀ (by norm_num))
    (by exact_mod_cast hA) (FixedPointComplex.eps_pos _).le (convPrecision_small k A)
  simpa only [convolutionError, frequencyError, forwardError, fftError, four_pow_fft_length,
    zero_add, mul_zero, add_zero, show 2 * k = k * 2 by omega, pow_mul, mul_assoc] using h

theorem convPrecision_linear (k A : ℕ) :
    convPrecision k A ≤ 5 * k + 2 * A.log2 + 16 := by
  by_cases hA : A = 0
  · subst A
    simp [convPrecision]
    omega
  have h : A < 2 ^ (A.log2 + 1) := Nat.lt_log2_self
  have hs : A ^ 2 < (2 ^ (A.log2 + 1)) ^ 2 := by nlinarith
  have hp : 2048 * A ^ 2 < 2 ^ (2 * A.log2 + 13) := by
    have hm := Nat.mul_lt_mul_of_pos_left hs (by norm_num : 0 < 2048)
    calc
      _ < 2048 * (2 ^ (A.log2 + 1)) ^ 2 := hm
      _ = 2 ^ (2 * A.log2 + 13) := by
        rw [← pow_mul, show (2048 : ℕ) = 2 ^ 11 by norm_num, ← pow_add]
        congr 1
        omega
  have hl := (Nat.log2_lt (by positivity : 2048 * A ^ 2 ≠ 0)).mpr hp
  unfold convPrecision
  omega

/-- Integer zero padding; the executable input reader never evaluates a complex scalar. -/
def zeroPadInt {q : ℕ} (a : CyclicRing.Cyclic q) (i : ℕ) : ℤ :=
  if h : i < q then a ⟨i, h⟩ else 0

theorem zeroPadInt_eq_polynomial {q : ℕ} (a : CyclicRing.Cyclic q) :
    zeroPadInt a = (PolynomialCyclicFold.toPolynomial a).coeff := by
  funext i
  by_cases hi : i < q
  · simp only [zeroPadInt, dif_pos hi]
    rw [PolynomialCyclicFold.coeff_toPolynomial a ⟨i, hi⟩]
  · simp only [zeroPadInt, dif_neg hi,
      PolynomialCyclicFold.coeff_toPolynomial_eq_zero a i (by omega)]

/-- Integer-only cyclic multiplication. The two ordinary product positions are
added as cells before nearest-integer recovery. -/
def cyclic {q : ℕ} (B k : ℕ) (a b : CyclicRing.Cyclic q) : FastConvolution.Counted (List ℤ) :=
  let product := convolution B k (zeroPadInt a) (zeroPadInt b)
  let output := FastConvolution.Counted.sequence (fun j =>
    ⟨FixedPointComplex.recover B (FixedPointComplex.add
      (product.value.getD j zero) (product.value.getD (j + q) zero)), 8 * B + 32⟩)
    (List.range q)
  ⟨output.value, product.operations + output.operations⟩

theorem cyclic_correct {q : ℕ} [NeZero q] (k A : ℕ) (hA : 1 ≤ A)
    (a b : CyclicRing.Cyclic q) (hN : 2 * q ≤ 2 ^ k)
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (A : ℝ)) (hb : ∀ i, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : Fin q) :
    (cyclic (convPrecision k A) k a b).value.getD j.val 0 = CyclicRing.convolution a b j := by
  let P := PolynomialCyclicFold.toPolynomial a
  let Q := PolynomialCyclicFold.toPolynomial b
  let B := convPrecision k A
  have hp : P.natDegree < 2 ^ k := lt_of_lt_of_le (FastConvolution.toPolynomial_natDegree_lt a) (by omega)
  have hq : Q.natDegree < 2 ^ k := lt_of_lt_of_le (FastConvolution.toPolynomial_natDegree_lt b) (by omega)
  have hpq : (P * Q).natDegree < 2 ^ k := by
    have hpd := FastConvolution.toPolynomial_natDegree_lt a
    have hqd := FastConvolution.toPolynomial_natDegree_lt b
    exact lt_of_le_of_lt Polynomial.natDegree_mul_le (by dsimp [P, Q]; omega)
  have hj : j.val < 2 ^ k := lt_of_lt_of_le j.isLt (by omega)
  have hjq : j.val + q < 2 ^ k := by have := j.isLt; omega
  have hpa : ∀ i < 2 ^ k, ‖(P.coeff i : ℂ)‖ ≤ (A : ℝ) := by
    intro i hi
    rw [← zeroPadInt_eq_polynomial a]
    by_cases h : i < q
    · simpa only [zeroPadInt, dif_pos h] using ha ⟨i, h⟩
    · simp only [zeroPadInt, dif_neg h, Int.cast_zero, norm_zero]
      positivity
  have hqb : ∀ i < 2 ^ k, ‖(Q.coeff i : ℂ)‖ ≤ (A : ℝ) := by
    intro i hi
    rw [← zeroPadInt_eq_polynomial b]
    by_cases h : i < q
    · simpa only [zeroPadInt, dif_pos h] using hb ⟨i, h⟩
    · simp only [zeroPadInt, dif_neg h, Int.cast_zero, norm_zero]
      positivity
  have he (i : ℕ) (hi : i < 2 ^ k) := convolution_integer_error B k P Q (A : ℝ)
    (by positivity) (convPrecision_eps_le k A) hpa hqb hp hq hpq i hi
  change (FastConvolution.Counted.sequence (fun i =>
    ⟨FixedPointComplex.recover B (FixedPointComplex.add
      ((convolution B k (zeroPadInt a) (zeroPadInt b)).value.getD i zero)
      ((convolution B k (zeroPadInt a) (zeroPadInt b)).value.getD (i + q) zero)), 8 * B + 32⟩)
    (List.range q)).value.getD j.val 0 = _
  rw [FastConvolution.Counted.sequence_value, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  rw [zeroPadInt_eq_polynomial a, zeroPadInt_eq_polynomial b]
  apply FixedPointComplex.recover_correct
  have hadd := FixedPointComplex.add_error B
    ((convolution B k P.coeff Q.coeff).value.getD j.val zero)
    ((convolution B k P.coeff Q.coeff).value.getD (j.val + q) zero)
    ((P * Q).coeff j.val : ℂ) ((P * Q).coeff (j.val + q) : ℂ)
    (convolutionError B k (A : ℝ)) (convolutionError B k (A : ℝ)) (he j.val hj) (he _ hjq)
  rw [PolynomialCyclicFold.convolution_eq_coeff_fold]
  push_cast
  exact hadd.trans_lt (by simpa only [two_mul] using convolutionError_small k A hA)

theorem pointwise_operations (B N : ℕ) (a b : List FixedPointComplex.Cell) :
    (pointwise B N a b).operations = (2 * B + 8) * N := by
  unfold pointwise
  rw [FastConvolution.Counted.sequence_operations _ _ (2 * B + 8) (by intros; rfl), List.length_range]

theorem normalizeVector_operations (N : ℕ) (a : List FixedPointComplex.Cell) :
    (normalizeVector N a).operations = 2 * N := by
  unfold normalizeVector
  rw [FastConvolution.Counted.sequence_operations _ _ 2 (by intros; rfl), List.length_range]

/-- The arithmetic ledger includes all three rounded FFTs, every raw root
synthesis, conversion, pointwise product, input scaling and normalization. -/
theorem convolution_operations (B k : ℕ) (a b : ℕ → ℤ) :
    (convolution B k a b).operations ≤
      3 * k * 2 ^ k * fftUnitCost B + (4 * B + 14) * 2 ^ k := by
  have hl := fft_operations B k false (fun i => embed B (a i))
  have hr := fft_operations B k false (fun i => embed B (b i))
  have hi := fft_operations B k true (fun i =>
    (pointwise B (2 ^ k) (fft B false k (fun t => embed B (a t))).value
      (fft B false k (fun t => embed B (b t))).value).value.getD i zero)
  simp only [convolution, pointwise_operations, normalizeVector_operations]
  nlinarith

theorem cyclic_operations {q : ℕ} (B k : ℕ) (a b : CyclicRing.Cyclic q) :
    (cyclic B k a b).operations ≤
      3 * k * 2 ^ k * fftUnitCost B + (4 * B + 14) * 2 ^ k + (8 * B + 32) * q := by
  have hc := convolution_operations B k (zeroPadInt a) (zeroPadInt b)
  simp only [cyclic]
  rw [FastConvolution.Counted.sequence_operations _ _ (8 * B + 32) (by intros; rfl), List.length_range]
  exact Nat.add_le_add_right hc _

def multiplication {q : ℕ} (A : ℕ) (a b : CyclicRing.Cyclic q) : FastConvolution.Counted (List ℤ) :=
  let k := FastConvolution.paddedExponent q
  cyclic (convPrecision k A) k a b

theorem multiplication_correct {q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (a b : CyclicRing.Cyclic q) (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : Fin q) :
    (multiplication A a b).value.getD j.val 0 = CyclicRing.convolution a b j :=
  cyclic_correct _ _ hA a b (FastConvolution.padded_length_bounds q (NeZero.pos q)).1 ha hb j

/-- An explicit quasilinear-in-length arithmetic count with polynomial precision
cost. Root synthesis is charged separately at each actual butterfly output. -/
theorem multiplication_operations {q : ℕ} [NeZero q] (A : ℕ) (a b : CyclicRing.Cyclic q) :
    let k := FastConvolution.paddedExponent q
    let B := convPrecision k A
    (multiplication A a b).operations ≤
      12 * k * q * (100 * (B + k + 78) ^ 2 + 8 * B + 64) + (24 * B + 88) * q := by
  let k := FastConvolution.paddedExponent q
  let B := convPrecision k A
  have hc := cyclic_operations B k a b
  have hN := (FastConvolution.padded_length_bounds q (NeZero.pos q)).2
  have hR := RationalWorkBounds.rootOperations_polynomial B k
  have hC : fftUnitCost B ≤ 100 * (B + k + 78) ^ 2 + 8 * B + 64 := by
    unfold fftUnitCost
    omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left (3 * k) hN) hC
  have hadd := Nat.mul_le_mul_left (4 * B + 14) hN
  change (cyclic B k a b).operations ≤ _
  nlinarith


theorem fft_decoded_norm_bound (B k : ℕ) (inverse : Bool)
    (a : ℕ → FixedPointComplex.Cell) (x : ℕ → ℂ) (A E : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖x i‖ ≤ A)
    (hx : ∀ i < 2 ^ k, ‖FixedPointComplex.decode B (a i) - x i‖ ≤ E)
    (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((fft B inverse k a).value.getD j zero)‖ ≤
      fftError B k A E + (2 : ℝ) ^ k * A := by
  exact (norm_le_norm_sub_add _ _).trans
    (add_le_add (fft_error B k inverse a x A E hA hE heps ha hx j hj)
      (radixFFT_norm k (omega k inverse) x A hA (omega_norm _ _).le ha j))

theorem fft_decoded_bits_of_small (B k A : ℕ) (inverse : Bool)
    (a : ℕ → FixedPointComplex.Cell) (x : ℕ → ℂ) (E : ℝ)
    (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖x i‖ ≤ (A : ℝ))
    (hx : ∀ i < 2 ^ k, ‖FixedPointComplex.decode B (a i) - x i‖ ≤ E)
    (hsmall : fftError B k A E ≤ 1) (j : ℕ) (hj : j < 2 ^ k) :
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ k * A + 1))
      ((fft B inverse k a).value.getD j zero) := by
  apply FixedPointComplex.decoded_bits
  have hn := fft_decoded_norm_bound B k inverse a x A E (Nat.cast_nonneg _) hE heps ha hx j hj
  push_cast
  linarith


theorem fftError_mono_depth (B l k : ℕ) (A E : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hl : l ≤ k) :
    fftError B l A E ≤ fftError B k A E := by
  unfold fftError
  have hc : 0 ≤ E + (A + 1) * FixedPointComplex.eps B := by
    have he := (FixedPointComplex.eps_pos B).le
    positivity
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (show (1 : ℝ) ≤ 4 by norm_num) (Nat.add_le_add_right hl 1)) hc

theorem fft_subcall_bits_of_small (B l k A : ℕ) (inverse : Bool)
    (a : ℕ → FixedPointComplex.Cell) (x : ℕ → ℂ) (E : ℝ)
    (hl : l ≤ k) (hE : 0 ≤ E) (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ l, ‖x i‖ ≤ (A : ℝ))
    (hx : ∀ i < 2 ^ l, ‖FixedPointComplex.decode B (a i) - x i‖ ≤ E)
    (hsmall : fftError B k A E ≤ 1) (j : ℕ) (hj : j < 2 ^ l) :
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ k * A + 1))
      ((fft B inverse l a).value.getD j zero) := by
  apply FixedPointComplex.decoded_bits
  have hm := fftError_mono_depth B l k A E (Nat.cast_nonneg _) hE hl
  have hn := fft_decoded_norm_bound B l inverse a x A E (Nat.cast_nonneg _) hE heps ha hx j hj
  have hpow : (2 : ℝ) ^ l * A ≤ 2 ^ k * A :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (Nat.cast_nonneg A)
  push_cast
  linarith

theorem fft_strided_subcall_bits (B l r k t A : ℕ) (inverse : Bool)
    (a : ℕ → FixedPointComplex.Cell) (x : ℕ → ℂ) (E : ℝ)
    (hlr : l + r ≤ k) (ht : t < 2 ^ r) (hE : 0 ≤ E)
    (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖x i‖ ≤ (A : ℝ))
    (hx : ∀ i < 2 ^ k, ‖FixedPointComplex.decode B (a i) - x i‖ ≤ E)
    (hsmall : fftError B k A E ≤ 1) (j : ℕ) (hj : j < 2 ^ l) :
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ k * A + 1))
      ((fft B inverse l (fun i => a (2 ^ r * i + t))).value.getD j zero) := by
  have hindex (i : ℕ) (hi : i < 2 ^ l) : 2 ^ r * i + t < 2 ^ k := by
    have hm : 2 ^ r * (i + 1) ≤ 2 ^ r * 2 ^ l := Nat.mul_le_mul_left _ (by omega)
    have hp : 2 ^ r * 2 ^ l ≤ 2 ^ k := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith
  exact fft_subcall_bits_of_small B l k A inverse
    (fun i => a (2 ^ r * i + t)) (fun i => x (2 ^ r * i + t)) E (by omega) hE heps
    (fun i hi => ha _ (hindex i hi)) (fun i hi => hx _ (hindex i hi)) hsmall j hj



theorem convPrecision_intermediate_errors (k A : ℕ) (hA : 1 ≤ A) :
    let B := convPrecision k A
    forwardError B k A ≤ 1 ∧ frequencyError B k A ≤ 1 ∧
      fftError B k ((2 : ℝ) ^ (2 * k) * (A : ℝ) ^ 2) (frequencyError B k A) ≤ 1 := by
  let B := convPrecision k A
  let N : ℝ := 2 ^ k
  let e := FixedPointComplex.eps B
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have he : 0 ≤ e := (FixedPointComplex.eps_pos B).le
  have hs : 512 * N ^ 5 * (A : ℝ) ^ 2 * e < 1 / 2 := convPrecision_small k A
  have hFb : forwardError B k A ≤ 8 * N ^ 2 * A * e := by
    simpa only [forwardError, fftError, four_pow_fft_length, zero_add, mul_assoc] using
      pipeline_forward_bound N A e hAr he
  have hFs : forwardError B k A ≤ 1 := hFb.trans (pipeline_forward_small N A e hN hAr he hs)
  have hF : 0 ≤ forwardError B k A := by
    unfold forwardError fftError
    have hep := (FixedPointComplex.eps_pos B).le
    positivity
  have hPb : frequencyError B k A ≤ 25 * N ^ 3 * (A : ℝ) ^ 2 * e := by
    exact pipeline_pointwise_bound N A e (forwardError B k A) hN hAr he hF hFs hFb
  have hN35 : N ^ 3 ≤ N ^ 5 := pow_le_pow_right₀ hN (by norm_num)
  have hPm : 25 * N ^ 3 * (A : ℝ) ^ 2 * e ≤ 512 * N ^ 5 * (A : ℝ) ^ 2 * e := by
    have hm := mul_le_mul_of_nonneg_right hN35 (show 0 ≤ (A : ℝ) ^ 2 * e by positivity)
    nlinarith [mul_nonneg (show 0 ≤ N ^ 5 by positivity) (show 0 ≤ (A : ℝ) ^ 2 * e by positivity)]
  have hPs : frequencyError B k A ≤ 1 := by linarith
  have hdim : (2 : ℝ) ^ (2 * k) = N ^ 2 := by
    dsimp [N]
    rw [mul_comm 2 k, pow_mul]
  have hIb : fftError B k ((2 : ℝ) ^ (2 * k) * (A : ℝ) ^ 2) (frequencyError B k A) ≤
      108 * N ^ 5 * (A : ℝ) ^ 2 * e := by
    simpa only [fftError, four_pow_fft_length, hdim] using
      pipeline_inverse_bound N A e (frequencyError B k A) hN hAr he hPb
  have hIm : 108 * N ^ 5 * (A : ℝ) ^ 2 * e ≤ 512 * N ^ 5 * (A : ℝ) ^ 2 * e := by
    have hm : 0 ≤ N ^ 5 * (A : ℝ) ^ 2 * e := by positivity
    nlinarith
  exact ⟨hFs, hPs, by linarith⟩




def frequencyCells (B k : ℕ) (a b : ℕ → ℤ) : List FixedPointComplex.Cell :=
  (pointwise B (2 ^ k)
    (fft B false k (fun i => embed B (a i))).value
    (fft B false k (fun i => embed B (b i))).value).value

theorem frequencyCells_error (B k : ℕ) (a b : ℕ → ℤ) (A : ℝ) (hA : 0 ≤ A)
    (heps : FixedPointComplex.eps B ≤ 1 / 2)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ A)
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ A) (j : ℕ) (hj : j < 2 ^ k) :
    ‖FixedPointComplex.decode B ((frequencyCells B k a b).getD j zero) -
      FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) j *
      FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) j‖ ≤ frequencyError B k A := by
  let f := fun i => FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) i
  let g := fun i => FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) i
  have hF := forward_error B k a A hA heps ha j hj
  have hG := forward_error B k b A hA heps hb j hj
  have hnF : ‖f j‖ ≤ (2 : ℝ) ^ k * A :=
    radixFFT_norm k _ _ A hA (omega_norm _ _).le ha j
  have hnG : ‖g j‖ ≤ (2 : ℝ) ^ k * A :=
    radixFFT_norm k _ _ A hA (omega_norm _ _).le hb j
  have hGsize : ‖FixedPointComplex.decode B
      ((fft B false k (fun i => embed B (b i))).value.getD j zero)‖ ≤
      (2 : ℝ) ^ k * A + forwardError B k A := by
    have h := (norm_le_norm_sub_add _ (g j)).trans (add_le_add hG hnG)
    linarith
  simp only [frequencyCells, pointwise_getD B (2 ^ k) _ _ j hj]
  have h := FixedPointComplex.mul_error B
    ((fft B false k (fun i => embed B (a i))).value.getD j zero)
    ((fft B false k (fun i => embed B (b i))).value.getD j zero)
    (f j) (g j) (forwardError B k A) (forwardError B k A) hF hG
  apply h.trans
  unfold frequencyError
  have hFnonneg : 0 ≤ forwardError B k A := (norm_nonneg _).trans hF
  gcongr

theorem frequency_exact_norm (k A : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : ℕ) :
    ‖FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) j *
      FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) j‖ ≤
      (2 ^ (2 * k) * A ^ 2 : ℕ) := by
  have hf := radixFFT_norm k (omega k false) (fun t => (a t : ℂ)) (A : ℝ)
    (Nat.cast_nonneg _) (omega_norm k false).le ha j
  have hg := radixFFT_norm k (omega k false) (fun t => (b t : ℂ)) (A : ℝ)
    (Nat.cast_nonneg _) (omega_norm k false).le hb j
  rw [norm_mul]
  calc
    _ ≤ ((2 : ℝ) ^ k * A) * ((2 : ℝ) ^ k * A) :=
      mul_le_mul hf hg (norm_nonneg _) (by positivity)
    _ = _ := by push_cast; rw [mul_comm 2 k, pow_mul]; ring

theorem forward_subcall_bits (k A l r t : ℕ) (a : ℕ → ℤ) (hA : 1 ≤ A)
    (hlr : l + r ≤ k) (ht : t < 2 ^ r)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ (A : ℝ)) (j : ℕ) (hj : j < 2 ^ l) :
    let B := convPrecision k A
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ k * A + 1))
      ((fft B false l (fun i => embed B (a (2 ^ r * i + t)))).value.getD j zero) := by
  let B := convPrecision k A
  apply fft_strided_subcall_bits B l r k t A false
    (fun i => embed B (a i)) (fun i => (a i : ℂ)) 0 hlr ht (by norm_num)
    (convPrecision_eps_le k A) ha
  · intro i hi
    simp [decode_embed]
  · exact (convPrecision_intermediate_errors k A hA).1
  · exact hj

theorem inverse_subcall_bits (k A l r t : ℕ) (a b : ℕ → ℤ) (hA : 1 ≤ A)
    (hlr : l + r ≤ k) (ht : t < 2 ^ r)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : ℕ) (hj : j < 2 ^ l) :
    let B := convPrecision k A
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ k * (2 ^ (2 * k) * A ^ 2) + 1))
      ((fft B true l (fun i => (frequencyCells B k a b).getD (2 ^ r * i + t) zero)).value.getD j zero) := by
  let B := convPrecision k A
  let f := fun i => FastConvolution.radixFFT k (omega k false) (fun t => (a t : ℂ)) i *
    FastConvolution.radixFFT k (omega k false) (fun t => (b t : ℂ)) i
  have hfreq : 0 ≤ frequencyError B k A := by
    unfold frequencyError forwardError fftError
    have he := (FixedPointComplex.eps_pos B).le
    positivity
  apply fft_strided_subcall_bits B l r k t (2 ^ (2 * k) * A ^ 2) true
    (fun i => (frequencyCells B k a b).getD i zero) f (frequencyError B k A) hlr ht hfreq
    (convPrecision_eps_le k A)
  · intro i hi
    exact frequency_exact_norm k A a b ha hb i
  · intro i hi
    exact frequencyCells_error B k a b A (Nat.cast_nonneg _) (convPrecision_eps_le k A) ha hb i hi
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (convPrecision_intermediate_errors k A hA).2.2
  · exact hj


/-- Raw rational conversion covers its multiplied numerators before division;
it does not assume bounded-size reduced rational arithmetic. -/
theorem ofRaw_working_bits (B R : ℕ) (r : RationalWorkBounds.Raw)
    (hr : RationalWorkBounds.Fits r R) :
    FixedPointComplex.FitsMagnitudeBits (R + B + 1) (r.re * FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (R + B + 1) (r.im * FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (R + 1) (r.den : ℤ) ∧
    FixedPointComplex.CellFits (R + B + 1) (ofRaw B r) := by
  have hc : ∀ z : ℤ, z.natAbs ≤ 2 ^ R →
      FixedPointComplex.FitsMagnitudeBits (R + B + 1) (z * FixedPointComplex.scaleZ B) := by
    intro z hz
    unfold FixedPointComplex.FitsMagnitudeBits
    rw [Int.natAbs_mul, FixedPointComplex.scaleZ, Int.natAbs_pow]
    norm_num only [Int.natAbs_ofNat']
    calc
      z.natAbs * 2 ^ B ≤ 2 ^ R * 2 ^ B := Nat.mul_le_mul_right _ hz
      _ = 2 ^ (R + B) := (pow_add ..).symm
      _ < 2 ^ (R + B + 1) := by
        rw [pow_succ]
        have h : 0 < (2 : ℕ) ^ (R + B) := by positivity
        omega
  have hdiv (z : ℤ) : (z / (r.den : ℤ)).natAbs ≤ z.natAbs := Int.natAbs_ediv_le_natAbs _ _
  refine ⟨hc _ hr.1, hc _ hr.2.1, ?_, ?_, ?_⟩
  · unfold FixedPointComplex.FitsMagnitudeBits
    simp only [Int.natAbs_natCast]
    apply hr.2.2.trans_lt
    rw [pow_succ]
    have h : 0 < (2 : ℕ) ^ R := by positivity
    omega
  · exact (hdiv _).trans_lt (hc _ hr.1)
  · exact (hdiv _).trans_lt (hc _ hr.2.1)

/-- Operand norm bounds cover both pre-division complex multiplication
numerators, and the rounded output. -/
theorem decoded_mul_working_bits (B M : ℕ) (x y : FixedPointComplex.Cell)
    (hx : ‖FixedPointComplex.decode B x‖ ≤ (M : ℝ))
    (hy : ‖FixedPointComplex.decode B y‖ ≤ (M : ℝ)) :
    FixedPointComplex.FitsMagnitudeBits (FixedPointComplex.productBits B M) (FixedPointComplex.mulRe x y) ∧
    FixedPointComplex.FitsMagnitudeBits (FixedPointComplex.productBits B M) (FixedPointComplex.mulIm x y) ∧
    FixedPointComplex.CellFits (FixedPointComplex.productBits B M) (FixedPointComplex.mul B x y) :=
  FixedPointComplex.mul_working_bits B M x y
    (FixedPointComplex.decoded_cell_bound B M x hx) (FixedPointComplex.decoded_cell_bound B M y hy)

theorem twiddle_norm_le_two (B k : ℕ) (inverse : Bool) (j : ℕ) (hj : j < 2 ^ k)
    (heps : FixedPointComplex.eps B ≤ 1 / 2) :
    ‖FixedPointComplex.decode B (twiddle B k inverse j)‖ ≤ 2 := by
  have he := twiddle_error B k inverse j hj
  have hn : ‖omega k inverse ^ j‖ = 1 := by rw [norm_pow, omega_norm, one_pow]
  have h := (norm_le_norm_sub_add (FixedPointComplex.decode B (twiddle B k inverse j))
    (omega k inverse ^ j)).trans (add_le_add he (le_of_eq hn))
  linarith

/-- A linear logarithmic bound for the largest FFT-stage cell allowance. -/
theorem stage_storedBits_linear (B k A : ℕ) :
    FixedPointComplex.storedBits B (2 ^ (3 * k) * A ^ 2 + 1) ≤
      B + 3 * k + 2 * A.log2 + 4 := by
  have ha : A < 2 ^ (A.log2 + 1) := Nat.lt_log2_self
  have hs : A ^ 2 < (2 ^ (A.log2 + 1)) ^ 2 := by nlinarith
  have hm := Nat.mul_lt_mul_of_pos_left hs (by positivity : 0 < (2 : ℕ) ^ (3 * k))
  have hp : 2 ^ (3 * k) * (2 ^ (A.log2 + 1)) ^ 2 = 2 ^ (3 * k + 2 * A.log2 + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hp] at hm
  have hn : 2 ^ (3 * k) * A ^ 2 + 1 < 2 ^ (3 * k + 2 * A.log2 + 3) := by
    calc
      2 ^ (3 * k) * A ^ 2 + 1 ≤ 2 ^ (3 * k + 2 * A.log2 + 2) := by omega
      _ < 2 ^ (3 * k + 2 * A.log2 + 2) * 2 := by
        have h : 0 < (2 : ℕ) ^ (3 * k + 2 * A.log2 + 2) := by positivity
        omega
      _ = 2 ^ (3 * k + 2 * A.log2 + 3) := by
        rw [← pow_succ]
  have hl := (Nat.log2_lt (by positivity : 2 ^ (3 * k) * A ^ 2 + 1 ≠ 0)).mpr hn
  unfold FixedPointComplex.storedBits
  omega


theorem multiplication_operations_logarithmic {q : ℕ} [NeZero q] (A : ℕ)
    (a b : CyclicRing.Cyclic q) :
    let k := FastConvolution.paddedExponent q
    (multiplication A a b).operations ≤
      45000 * (k + 1) * q * (k + A.log2 + 100) ^ 2 := by
  let k := FastConvolution.paddedExponent q
  let B := convPrecision k A
  let S := k + A.log2 + 100
  have hc := multiplication_operations A a b
  change (multiplication A a b).operations ≤ _
  have hB : B ≤ 5 * S := by have := convPrecision_linear k A; dsimp [B, S]; omega
  have hT : B + k + 78 ≤ 6 * S := by have := convPrecision_linear k A; dsimp [B, S]; omega
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



theorem multiplication_correct_natAbs {q : ℕ} [NeZero q] (A : ℕ) (hA : 1 ≤ A)
    (a b : CyclicRing.Cyclic q) (ha : ∀ i, (a i).natAbs ≤ A)
    (hb : ∀ i, (b i).natAbs ≤ A) (j : Fin q) :
    (multiplication A a b).value.getD j.val 0 = CyclicRing.convolution a b j := by
  apply multiplication_correct A hA a b _ _ j
  · intro i
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast ha i
  · intro i
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hb i

theorem frequencyCells_bits (k A : ℕ) (a b : ℕ → ℤ) (hA : 1 ≤ A)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : ℕ) (hj : j < 2 ^ k) :
    let B := convPrecision k A
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ (2 * k) * A ^ 2 + 1))
      ((frequencyCells B k a b).getD j zero) := by
  let B := convPrecision k A
  apply FixedPointComplex.decoded_bits
  have he := frequencyCells_error B k a b A (Nat.cast_nonneg _) (convPrecision_eps_le k A) ha hb j hj
  have hn := frequency_exact_norm k A a b ha hb j
  have hs := (convPrecision_intermediate_errors k A hA).2.1
  have h := (norm_le_norm_sub_add _ _).trans (add_le_add he hn)
  calc
    _ ≤ frequencyError B k A + ((2 ^ (2 * k) * A ^ 2 : ℕ) : ℝ) := h
    _ ≤ 1 + ((2 ^ (2 * k) * A ^ 2 : ℕ) : ℝ) := add_le_add hs (le_refl _)
    _ = _ := by push_cast; ring

theorem normalize_preserves_bits (N D : ℕ) (c : FixedPointComplex.Cell)
    (hc : FixedPointComplex.CellFits D c) : FixedPointComplex.CellFits D (normalize N c) :=
  ⟨(Int.natAbs_ediv_le_natAbs _ _).trans_lt hc.1,
    (Int.natAbs_ediv_le_natAbs _ _).trans_lt hc.2⟩

theorem normalized_convolution_bits (k A : ℕ) (a b : ℕ → ℤ) (hA : 1 ≤ A)
    (ha : ∀ i < 2 ^ k, ‖(a i : ℂ)‖ ≤ (A : ℝ))
    (hb : ∀ i < 2 ^ k, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : ℕ) (hj : j < 2 ^ k) :
    let B := convPrecision k A
    FixedPointComplex.CellFits (FixedPointComplex.storedBits B (2 ^ (3 * k) * A ^ 2 + 1))
      ((convolution B k a b).value.getD j zero) := by
  let B := convPrecision k A
  have hi := inverse_subcall_bits k A k 0 0 a b hA (by omega) (by norm_num) ha hb j hj
  have hp : 2 ^ k * (2 ^ (2 * k) * A ^ 2) = 2 ^ (3 * k) * A ^ 2 := by
    rw [← mul_assoc, ← pow_add, show k + 2 * k = 3 * k by omega]
  simp only [pow_zero, one_mul, add_zero, hp] at hi
  change FixedPointComplex.CellFits _
    ((normalizeVector (2 ^ k) (fft B true k (fun i => (frequencyCells B k a b).getD i zero)).value).value.getD j zero)
  rw [normalizeVector_getD _ _ j hj]
  exact normalize_preserves_bits _ _ _ hi

theorem add_cell_bits (D : ℕ) (x y : FixedPointComplex.Cell)
    (hx : FixedPointComplex.CellFits D x) (hy : FixedPointComplex.CellFits D y) :
    FixedPointComplex.CellFits (D + 1) (FixedPointComplex.add x y) := by
  have h (a b : ℤ) (ha : a.natAbs < 2 ^ D) (hb : b.natAbs < 2 ^ D) :
      (a + b).natAbs < 2 ^ (D + 1) := by
    calc
      _ ≤ a.natAbs + b.natAbs := Int.natAbs_add_le _ _
      _ < 2 ^ D + 2 ^ D := Nat.add_lt_add ha hb
      _ = _ := by rw [pow_succ]; omega
  exact ⟨h _ _ hx.1 hy.1, h _ _ hx.2 hy.2⟩

theorem recover_working_bits (B D : ℕ) (c : FixedPointComplex.Cell)
    (hB : B ≤ D) (hc : FixedPointComplex.CellFits D c) :
    FixedPointComplex.FitsMagnitudeBits (D + 2) (2 * c.re + FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (D + 2) (2 * FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (D + 2) (FixedPointComplex.recover B c) := by
  have hs : 2 ^ B ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) hB
  have hp : (2 : ℕ) ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
  have ht : (2 : ℤ).natAbs = 2 := rfl
  have hn : (2 * c.re + FixedPointComplex.scaleZ B).natAbs < 2 ^ (D + 2) := by
    change (2 * c.re + (2 : ℤ) ^ B).natAbs < _
    have h := Int.natAbs_add_le (2 * c.re) (FixedPointComplex.scaleZ B)
    simp only [Int.natAbs_mul, FixedPointComplex.scaleZ, Int.natAbs_pow, ht] at h
    rw [hp]
    have hc' := hc.1
    unfold FixedPointComplex.FitsMagnitudeBits at hc'
    calc
      _ ≤ 2 * c.re.natAbs + 2 ^ B := h
      _ < 2 * 2 ^ D + 2 ^ B := Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hc' (by decide)) _
      _ ≤ 2 * 2 ^ D + 2 ^ D := Nat.add_le_add_left hs _
      _ < 4 * 2 ^ D := by
        have hp' : 0 < (2 : ℕ) ^ D := by positivity
        omega
  have hd : (2 * FixedPointComplex.scaleZ B).natAbs < 2 ^ (D + 2) := by
    simp only [Int.natAbs_mul, FixedPointComplex.scaleZ, Int.natAbs_pow, ht]
    rw [hp]
    have : 0 < (2 : ℕ) ^ D := by positivity
    omega
  exact ⟨hn, hd, (Int.natAbs_ediv_le_natAbs _ _).trans_lt hn⟩

theorem cyclic_recovery_working_bits {q : ℕ} [NeZero q] (k A : ℕ) (hA : 1 ≤ A)
    (a b : CyclicRing.Cyclic q) (hN : 2 * q ≤ 2 ^ k)
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (A : ℝ)) (hb : ∀ i, ‖(b i : ℂ)‖ ≤ (A : ℝ)) (j : Fin q) :
    let B := convPrecision k A
    let D := FixedPointComplex.storedBits B (2 ^ (3 * k) * A ^ 2 + 1)
    let product := convolution B k (zeroPadInt a) (zeroPadInt b)
    let folded := FixedPointComplex.add (product.value.getD j.val zero) (product.value.getD (j.val + q) zero)
    FixedPointComplex.FitsMagnitudeBits (D + 3) (2 * folded.re + FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (D + 3) (2 * FixedPointComplex.scaleZ B) ∧
    FixedPointComplex.FitsMagnitudeBits (D + 3) (FixedPointComplex.recover B folded) := by
  let B := convPrecision k A
  let D := FixedPointComplex.storedBits B (2 ^ (3 * k) * A ^ 2 + 1)
  have hza : ∀ i < 2 ^ k, ‖(zeroPadInt a i : ℂ)‖ ≤ (A : ℝ) := by
    intro i hi
    by_cases h : i < q
    · simpa only [zeroPadInt, dif_pos h] using ha ⟨i, h⟩
    · simp only [zeroPadInt, dif_neg h, Int.cast_zero, norm_zero]; positivity
  have hzb : ∀ i < 2 ^ k, ‖(zeroPadInt b i : ℂ)‖ ≤ (A : ℝ) := by
    intro i hi
    by_cases h : i < q
    · simpa only [zeroPadInt, dif_pos h] using hb ⟨i, h⟩
    · simp only [zeroPadInt, dif_neg h, Int.cast_zero, norm_zero]; positivity
  have hj : j.val < 2 ^ k := by have := j.isLt; omega
  have hjq : j.val + q < 2 ^ k := by have := j.isLt; omega
  have h1 := normalized_convolution_bits k A (zeroPadInt a) (zeroPadInt b) hA hza hzb j.val hj
  have h2 := normalized_convolution_bits k A (zeroPadInt a) (zeroPadInt b) hA hza hzb (j.val + q) hjq
  have hadd := add_cell_bits D _ _ h1 h2
  have h := recover_working_bits B (D + 1) _ (by dsimp [D, FixedPointComplex.storedBits]; omega) hadd
  simpa only [show D + 1 + 2 = D + 3 by omega] using h


#print axioms multiplication_correct_natAbs
#print axioms frequencyCells_bits
#print axioms normalized_convolution_bits
#print axioms cyclic_recovery_working_bits
#print axioms multiplication_operations_logarithmic
#print axioms forward_subcall_bits
#print axioms inverse_subcall_bits
#print axioms ofRaw_working_bits
#print axioms decoded_mul_working_bits
#print axioms stage_storedBits_linear

#print axioms fft_strided_subcall_bits
#print axioms convPrecision_intermediate_errors
#print axioms convPrecision_linear

#print axioms multiplication_correct
#print axioms multiplication_operations

#print axioms convolutionError_small
#print axioms cyclic_correct

#print axioms twiddle_error
#print axioms radixFFT_norm
#print axioms fft_error
#print axioms fft_operations
#print axioms convolution_integer_error

end ThinMatrix.ApproximateConvolution
