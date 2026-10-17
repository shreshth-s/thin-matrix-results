import GoodSetConstruction
import IntegerNormalization
import LowChannelEnumeration
import GoodMapEmbedding

/-!
# Uniform good-map setup with stored vectors and integer bit scores

The executable `construct` never performs rational arithmetic. Conditional
scores have the common denominator 2^(r*r); the numerator is built by exact
bit subtraction and normalized bit multiplication, summed by normalized bit
addition, and compared only by a subtraction borrow on stored score bits.
The same strict comparison preserves the original first-tie column rule.

All binary columns and coefficient vectors are generated directly as stored
vectors. The finite zero-kernel loops replace abstract independence tests;
the actual candidate mask enumeration replaces candidate-Fintype enumeration.
Gamma is constructed once and its Boolean weights are stored before Delta.
The final good family is materialized by original finite kernel checks.

Counters model the proved bit-serial arithmetic primitives together with
bounded array/index/list setup instructions. Array/control addresses and F2
cells are bounded setup words; the conservative polynomial overhead includes
mask scans, index arrays, copies and comparisons. This module does not assert
a compilation of this finite setup model to LightModel. Natural/rational
score functions are denotational specifications only, outside `construct`'s
runtime dependency graph. All maintained score magnitudes have O(L^2) bits.
-/

namespace ThinMatrix.GoodMapRuntime
open scoped BigOperators
open GoodSets

def integerNumerator (r f : ℕ) : ℕ :=
  (∏ j ∈ Finset.Ico f r, (2^r - 2^j)) * 2^(r*f)

lemma dyadic_product (n r f : ℕ) (hr : f+n=r) :
    (∏ j ∈ Finset.Ico f r, ((2^r-2^j : ℕ) : ℚ)) =
      (2:ℚ)^(r*n)*binarySuccess n := by
  induction n generalizing r f with
  | zero =>
      have he : f=r := by omega
      subst r
      simp [binarySuccess]
  | succ n ih =>
      have hfr : f<r := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hfr]
      rw [ih r (f+1) (by omega)]
      rw [binary_factor r f hfr, show r-f=n+1 by omega, binarySuccess_succ]
      simp only [Nat.mul_succ, pow_add]
      ring

theorem integerNumerator_eq (r f : ℕ) (hf : f≤r) :
    (integerNumerator r f : ℚ) = (2:ℚ)^(r*r)*binarySuccess (r-f) := by
  unfold integerNumerator
  rw [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat,
    dyadic_product (r-f) r f (by omega)]
  have he : r*(r-f)+r*f=r*r := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hf]
  calc
    _ = (2:ℚ)^(r*(r-f)+r*f)*binarySuccess (r-f) := by rw [pow_add]; ring
    _ = _ := by rw [he]

lemma binarySuccess_le_one (n : ℕ) : binarySuccess n ≤ 1 := by
  induction n with
  | zero => simp [binarySuccess]
  | succ n ih =>
      rw [binarySuccess_succ]
      have hμ : 0≤binarySuccess n := (binarySuccess_gt_quarter n).le.trans' (by norm_num)
      have hp : 0≤(1/2:ℚ)^(n+1) := by positivity
      calc
        _ ≤ binarySuccess n*1 := mul_le_mul_of_nonneg_left (by linarith) hμ
        _ ≤ 1 := by simpa using ih

theorem integerNumerator_le (r f : ℕ) (hf : f≤r) :
    integerNumerator r f ≤ 2^(r*r) := by
  have h : (integerNumerator r f : ℚ) ≤ (2:ℚ)^(r*r) := by
    rw [integerNumerator_eq r f hf]
    simpa using mul_le_mul_of_nonneg_left (binarySuccess_le_one (r-f))
      (show 0≤(2:ℚ)^(r*r) by positivity)
  exact_mod_cast h

def scaleEntry {A : Type*} (c : ℚ) (entry : A × ℕ) : A × ℚ :=
  (entry.1,c*entry.2)

def integerMaxFrom {A : Type*} (best : A × ℕ) : List (A × ℕ) → A × ℕ
  | [] => best
  | entry::rest => integerMaxFrom (if best.2<entry.2 then entry else best) rest

def integerMax {A : Type*} (fallback : A × ℕ) : List (A × ℕ) → A × ℕ
  | [] => fallback
  | best::rest => integerMaxFrom best rest

theorem cachedMaxFrom_scaled {A : Type*} (c : ℚ) (hc : 0<c)
    (best : A × ℕ) (entries : List (A × ℕ)) :
    GoodSetConstruction.cachedMaxFrom (scaleEntry c best) (entries.map (scaleEntry c)) =
      scaleEntry c (integerMaxFrom best entries) := by
  induction entries generalizing best with
  | nil => rfl
  | cons entry rest ih =>
      have hcompare : c*(best.2:ℚ)<c*(entry.2:ℚ) ↔ best.2<entry.2 := by
        rw [mul_lt_mul_iff_right₀ hc, Nat.cast_lt]
      change GoodSetConstruction.cachedMaxFrom
        (if c*(best.2:ℚ)<c*(entry.2:ℚ) then scaleEntry c entry else scaleEntry c best)
        (rest.map (scaleEntry c)) =
        scaleEntry c (integerMaxFrom (if best.2<entry.2 then entry else best) rest)
      by_cases h : best.2<entry.2
      · simpa only [if_pos h,if_pos (hcompare.mpr h)] using ih entry
      · simpa only [if_neg h,if_neg (fun ht => h (hcompare.mp ht))] using ih best

theorem cachedMax_scaled {A : Type*} (c : ℚ) (hc : 0<c)
    (fallback : A × ℕ) (entries : List (A × ℕ)) :
    GoodSetConstruction.cachedMax (scaleEntry c fallback) (entries.map (scaleEntry c)) =
      scaleEntry c (integerMax fallback entries) := by
  cases entries with
  | nil => rfl
  | cons best rest => exact cachedMaxFrom_scaled c hc best rest

open GoodSetConstruction

/-- Denominator-cleared reference score, used only for program refinement. -/
def integerPotential {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L)) (ell : ℕ) : ℕ :=
  if restrictionTest Γ (prefixSet Q ell) then integerNumerator r (prefixSet Q ell).card else 0

theorem integerPotential_scale {L r : ℕ} (Γ : BinaryMap r L) (Q : Finset (Fin L))
    (hQ : Q.card = r) (ell : ℕ) :
    (integerPotential Γ Q ell : ℚ) = (2:ℚ)^(r*r)*potential Γ Q ell := by
  have hf : (prefixSet Q ell).card ≤ r := by
    rw [←hQ]
    exact Finset.card_le_card (prefixSet_subset Q ell)
  unfold integerPotential potential
  split_ifs <;> simp [integerNumerator_eq r _ hf]

def integerScore {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → Bool) (Γ : BinaryMap r L) (ell : ℕ) : ℕ :=
  ∑ a, if weights a then integerPotential Γ (sets a) ell else 0

theorem integerScore_scale {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → Bool) (Γ : BinaryMap r L) (ell : ℕ) :
    (integerScore sets weights Γ ell : ℚ) =
      (2:ℚ)^(r*r)*score sets (fun a => if weights a then 1 else 0) Γ ell := by
  unfold integerScore score
  rw [Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  cases hw : weights a
  · simp [hw]
  · simpa [hw] using integerPotential_scale Γ (sets a) (hsets a) ell

theorem integerScore_le {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → Bool) (Γ : BinaryMap r L) (ell : ℕ) :
    integerScore sets weights Γ ell ≤ Fintype.card A*2^(r*r) := by
  unfold integerScore
  calc
    _ ≤ ∑ _a : A, 2^(r*r) := by
      apply Finset.sum_le_sum
      intro a ha
      split
      · unfold integerPotential
        split
        · exact integerNumerator_le r _ (by
            rw [←hsets a]
            exact Finset.card_le_card (prefixSet_subset (sets a) ell))
        · exact Nat.zero_le _
      · exact Nat.zero_le _
    _ = _ := by simp

def integerSelectColumn (r : ℕ) (sc : (Fin r → F₂) → ℕ) : Fin r → F₂ :=
  (integerMax (0,0) ((binaryColumns r).map (fun x => (x,sc x)))).1

theorem integerSelectColumn_eq (r : ℕ) (sc : (Fin r → F₂) → ℕ)
    (c : ℚ) (hc : 0<c) :
    integerSelectColumn r sc = selectColumn r (fun x => c*(sc x : ℚ)) := by
  unfold integerSelectColumn selectColumn
  rw [cacheScores_entries]
  have he : (binaryColumns r).map (fun x => (x,c*(sc x:ℚ))) =
      (((binaryColumns r).map (fun x => (x,sc x))).map (scaleEntry c)) := by
    simp only [List.map_map,Function.comp_def,scaleEntry]
  rw [he]
  have hs := cachedMax_scaled c hc (0,0) ((binaryColumns r).map (fun x => (x,sc x)))
  have hf : scaleEntry c ((0,0) : (Fin r → F₂) × ℕ) = (0,0) := by simp [scaleEntry]
  rw [hf] at hs
  rw [hs]
  rfl

def integerColumnStep {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → Bool) (ell : ℕ) (Γ : BinaryMap r L) : BinaryMap r L :=
  if he : ell<L then
    Function.update Γ ⟨ell,he⟩ (integerSelectColumn r
      (fun x => integerScore sets weights (Function.update Γ ⟨ell,he⟩ x) (ell+1)))
  else Γ

theorem integerColumnStep_eq {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → Bool) (ell : ℕ) (Γ : BinaryMap r L) :
    integerColumnStep sets weights ell Γ = columnStep sets (fun a => if weights a then 1 else 0) ell Γ := by
  unfold integerColumnStep columnStep
  split
  · have hscale (x : Fin r → F₂) :
        score sets (fun a => if weights a then 1 else 0) (Function.update Γ ⟨ell,‹ell<L›⟩ x) (ell+1) =
          ((2:ℚ)^(r*r))⁻¹*(integerScore sets weights (Function.update Γ ⟨ell,‹ell<L›⟩ x) (ell+1):ℚ) := by
      rw [integerScore_scale sets hsets]
      field_simp
    simp_rw [hscale]
    rw [integerSelectColumn_eq r _ (((2:ℚ)^(r*r))⁻¹) (inv_pos.mpr (by positivity))]
  · rfl

def integerBuildMap {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (weights : A → Bool) : ℕ → BinaryMap r L
  | 0 => 0
  | ell+1 => integerColumnStep sets weights ell (integerBuildMap sets weights ell)

theorem integerBuildMap_eq {A : Type*} [Fintype A] {L r : ℕ}
    (sets : A → Finset (Fin L)) (hsets : ∀ a, (sets a).card = r)
    (weights : A → Bool) (ell : ℕ) :
    integerBuildMap (r := r) sets weights ell = buildMap (r := r) sets (fun a => if weights a then 1 else 0) ell := by
  induction ell with
  | zero => rfl
  | succ ell ih => rw [integerBuildMap,buildMap,ih,integerColumnStep_eq sets hsets]

def integerConstructGoodMaps (L m : ℕ) : BinaryMap m L × BinaryMap (L-m) L :=
  let Γ := integerBuildMap (r := m) (fun Q : Candidate L m => (Q : Finset (Fin L))) (fun _ => true) L
  let Δ := integerBuildMap (r := L-m) (fun Q : Candidate L m => ((Q : Finset (Fin L))ᶜ))
    (fun Q => restrictionTest Γ Q) L
  (Γ,Δ)

theorem integerConstructGoodMaps_eq (L m : ℕ) :
    integerConstructGoodMaps L m = constructGoodMaps L m := by
  unfold integerConstructGoodMaps constructGoodMaps gammaMap constructMap deltaWith
  rw [integerBuildMap_eq _ candidate_size]
  simp only [ite_true]
  rw [integerBuildMap_eq _ candidate_compl_size]
  rfl

/-- Density is inherited for exactly the same constructed maps. -/
theorem integerConstructGoodMaps_density (L m : ℕ) :
    Nat.choose L m ≤ 16*Nat.card {Q : Candidate L m //
      Good (integerConstructGoodMaps L m).1 (integerConstructGoodMaps L m).2 Q} := by
  rw [integerConstructGoodMaps_eq]
  exact constructGoodMaps_correct L m

open IntegerArithmetic

/-- Direct bit construction of 2^n; no opaque integer-to-bits conversion. -/
def powerBits (n : ℕ) : SignedBits := ⟨false,List.replicate n false ++ [true]⟩

lemma value_false_prefix (n : ℕ) (xs : List Bool) :
    value (List.replicate n false ++ xs) = 2^n*value xs := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,value,ih,pow_succ]; ring

@[simp] theorem powerBits_value (n : ℕ) : signedValue (powerBits n) = (2^n : ℕ) := by
  simp [powerBits,signedValue,value_false_prefix,value]

@[simp] theorem powerBits_length (n : ℕ) : (powerBits n).magnitude.length = n+1 := by
  simp [powerBits]

/-- Exact factor subtraction, normalized before persistent storage. -/
def factorBits (r j : ℕ) : SignedBits × ℕ :=
  let a := powerBits r
  let b := powerBits j
  let sub := subCounted a.magnitude b.magnitude false
  let norm := normalizeCounted sub.1.1
  (⟨false,norm.1⟩,r+j+4+sub.2+norm.2)

theorem factorBits_value (r j : ℕ) (hj : j ≤ r) :
    signedValue (factorBits r j).1 = ((2^r-2^j : ℕ) : ℤ) := by
  unfold factorBits signedValue
  dsimp only
  simp only [Bool.false_eq_true,if_false,normalizeCounted_value,normalize_value,
    (subCounted_projections _ _ _).1]
  have hpow : value (powerBits j).magnitude ≤ value (powerBits r).magnitude := by
    simp only [powerBits,value_false_prefix,value,digit_true,mul_zero,
      add_zero,mul_one]
    exact Nat.pow_le_pow_right (by omega) hj
  rw [subBits_value _ _ hpow]
  simp [powerBits,value_false_prefix,value]

theorem factorBits_length (r j : ℕ) (hj : j ≤ r) :
    (factorBits r j).1.magnitude.length ≤ r+1 := by
  unfold factorBits
  dsimp only
  rw [normalizeCounted_value,(subCounted_projections _ _ _).1]
  have hn := normalize_length ((subBits (powerBits r).magnitude (powerBits j).magnitude false).1)
  rw [subBits_length,powerBits_length,powerBits_length] at hn
  omega

theorem factorBits_work (r j : ℕ) (hj : j ≤ r) :
    (factorBits r j).2 ≤ 32*(r+1) := by
  have hn := normalizeCounted_steps
    ((subCounted (powerBits r).magnitude (powerBits j).magnitude false).1.1)
  rw [(subCounted_projections _ _ _).1,subBits_length,powerBits_length,powerBits_length] at hn
  unfold factorBits
  dsimp only
  rw [(subCounted_projections _ _ _).2,columnSteps_eq,powerBits_length,powerBits_length,
    (subCounted_projections _ _ _).1]
  omega

def partialNumerator (r f n : ℕ) : ℕ :=
  (∏ j ∈ Finset.Ico f (f+n),(2^r-2^j))*2^(r*f)

@[simp] theorem partialNumerator_zero (r f : ℕ) : partialNumerator r f 0 = 2^(r*f) := by
  simp [partialNumerator]

theorem partialNumerator_step (r f n : ℕ) :
    partialNumerator r f (n+1) = partialNumerator r f n*(2^r-2^(f+n)) := by
  unfold partialNumerator
  rw [show f+(n+1) = f+n+1 by omega,Finset.prod_Ico_succ_top (by omega)]
  ring

theorem partialNumerator_bound (r f n : ℕ) :
    partialNumerator r f n ≤ 2^(r*f+r*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [partialNumerator_step]
      calc
        _ ≤ 2^(r*f+r*n)*2^r := Nat.mul_le_mul ih (Nat.sub_le _ _)
        _ = _ := by rw [←pow_add]; congr 1; ring

/-- Actual persistent bit multiplication loop for the cleared numerator. -/
def numeratorBits (r f : ℕ) : ℕ → SignedBits × ℕ
  | 0 => (powerBits (r*f),r*f+1)
  | n+1 =>
      let prev := numeratorBits r f n
      let factor := factorBits r (f+n)
      let product := normalizedMulCounted prev.1 factor.1
      (product.1,prev.2+factor.2+product.2+4)

theorem numeratorBits_value (r f n : ℕ) (hn : f+n ≤ r) :
    signedValue (numeratorBits r f n).1 = (partialNumerator r f n : ℤ) := by
  induction n with
  | zero => simp [numeratorBits]
  | succ n ih =>
      simp only [numeratorBits,normalizedMulCounted_value,ofInt_correct]
      rw [ih (by omega),factorBits_value r (f+n) (by omega),partialNumerator_step,Nat.cast_mul]

theorem numeratorBits_length (r f n : ℕ) (hn : f+n ≤ r) :
    (numeratorBits r f n).1.magnitude.length ≤ r*r+1 := by
  cases n with
  | zero =>
      simp only [numeratorBits,powerBits_length]
      have := Nat.mul_le_mul_left r (show f ≤ r by omega)
      omega
  | succ n =>
      simp only [numeratorBits,normalizedMulCounted_value]
      rw [ofInt_length]
      have hv : ((signedValue (numeratorBits r f n).1* signedValue (factorBits r (f+n)).1).natAbs) =
          partialNumerator r f (n+1) := by
        rw [numeratorBits_value r f n (by omega),factorBits_value r (f+n) (by omega),
          ←Nat.cast_mul,Int.natAbs_natCast,←partialNumerator_step]
      rw [hv]
      apply Nat.size_le.mpr
      have hb := partialNumerator_bound r f (n+1)
      have he : r*f+r*(n+1) ≤ r*r := by
        rw [←Nat.mul_add]
        exact Nat.mul_le_mul_left r hn
      have hp : 2^(r*f+r*(n+1)) ≤ 2^(r*r) := Nat.pow_le_pow_right (by decide) he
      have hstrict : 2^(r*r) < 2^(r*r+1) := by
        rw [pow_succ]
        have hpos : 0 < 2^(r*r) := by positivity
        omega
      omega

theorem numeratorBits_work (r f n : ℕ) (hn : f+n ≤ r) :
    (numeratorBits r f n).2 ≤ n*256*(r*r+r+4)^2+r*f+1 := by
  induction n with
  | zero => simp [numeratorBits]
  | succ n ih =>
      have hp := ih (by omega)
      have hlen := numeratorBits_length r f n (by omega)
      have hflen := factorBits_length r (f+n) (by omega)
      have hfac := factorBits_work r (f+n) (by omega)
      have hm := normalizedMulCounted_steps (numeratorBits r f n).1 (factorBits r (f+n)).1
      have ha : (numeratorBits r f n).1.magnitude.length+1 ≤ r*r+r+4 := by omega
      have hb : (numeratorBits r f n).1.magnitude.length+
          (factorBits r (f+n)).1.magnitude.length+2 ≤ r*r+r+4 := by omega
      have hmul : (normalizedMulCounted (numeratorBits r f n).1 (factorBits r (f+n)).1).2 ≤
          60*(r*r+r+4)^2+4 := by
        calc
          _ ≤ 60*((numeratorBits r f n).1.magnitude.length+1)*
              ((numeratorBits r f n).1.magnitude.length+(factorBits r (f+n)).1.magnitude.length+2)+4 := hm
          _ ≤ 60*(r*r+r+4)*(r*r+r+4)+4 :=
            Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 60 ha) hb) 4
          _ = _ := by ring
      simp only [numeratorBits]
      nlinarith

namespace Kernel

open scoped BigOperators
open GoodSets

abbrev Columns (L r : ℕ) := Vector (Vector F₂ r) L

def selected {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f) :
    Fin f → (Fin r → F₂) :=
  fun i j => (columns.get (indices.get i)).get j

structure Result (α : Type*) where
  value : α
  sites : ℕ

def allLoop {α : Type*} (check : α → Result Bool) : List α → Result Bool
  | [] => ⟨true, 1⟩
  | a :: rest =>
    let head := check a
    let tail := allLoop check rest
    ⟨head.value && tail.value, head.sites + tail.sites + 1⟩

theorem allLoop_true {α : Type*} (check : α → Result Bool) (xs : List α) :
    (allLoop check xs).value = true ↔ ∀ x ∈ xs, (check x).value = true := by
  induction xs with
  | nil => simp [allLoop]
  | cons a xs ih => simp [allLoop, ih]

theorem allLoop_sites {α : Type*} (check : α → Result Bool) (xs : List α)
    (K : ℕ) (h : ∀ x ∈ xs, (check x).sites ≤ K) :
    (allLoop check xs).sites ≤ xs.length * (K + 1) + 1 := by
  induction xs with
  | nil => simp [allLoop]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [allLoop, List.length_cons]
    nlinarith

/-- Sequential scalar dot loop. A column/index/coefficient/row read,
F₂ multiplication/addition, and loop overhead consume eight sites. -/
def dotLoop {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) (row : Fin r) : List (Fin f) → Result F₂
  | [] => ⟨0, 1⟩
  | i :: rest =>
    let scalar := coeff.get i
    let address := indices.get i
    let column := columns.get address
    let entry := column.get row
    let product := scalar * entry
    let tail := dotLoop columns indices coeff row rest
    ⟨product + tail.value, tail.sites + 8⟩

theorem dotLoop_value {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) (row : Fin r) (xs : List (Fin f)) :
    (dotLoop columns indices coeff row xs).value =
      (xs.map (fun i => coeff.get i * selected columns indices i row)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [dotLoop, selected, ih]

theorem dotLoop_sites {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) (row : Fin r) (xs : List (Fin f)) :
    (dotLoop columns indices coeff row xs).sites = 8 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [dotLoop, ih]; omega

def rowsZero {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) : Result Bool :=
  allLoop (fun row =>
    let sum := dotLoop columns indices coeff row (List.ofFn (id : Fin f → Fin f))
    ⟨decide (sum.value = 0), sum.sites + 1⟩)
    (List.ofFn (id : Fin r → Fin r))

theorem rowsZero_true {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) :
    (rowsZero columns indices coeff).value = true ↔
      (∑ i : Fin f, coeff.get i • selected columns indices i) = 0 := by
  simp only [rowsZero, allLoop_true, dotLoop_value, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, id_eq, decide_eq_true_eq]
  constructor
  · intro h
    funext row
    have hr := h row (List.mem_ofFn.mpr ⟨row, rfl⟩)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hr
  · intro h row _
    have hr := congrFun h row
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hr

def coeffZero {f : ℕ} (coeff : Vector F₂ f) : Result Bool :=
  allLoop (fun i => ⟨decide (coeff.get i = 0), 2⟩)
    (List.ofFn (id : Fin f → Fin f))

theorem coeffZero_true {f : ℕ} (coeff : Vector F₂ f) :
    (coeffZero coeff).value = true ↔ (fun i => coeff.get i) = 0 := by
  simp only [coeffZero, allLoop_true, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact h i (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h i _
    exact congrFun h i

def kernelEntry {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) : Result Bool :=
  let rows := rowsZero columns indices coeff
  let zero := coeffZero coeff
  ⟨if rows.value then zero.value else true, rows.sites + zero.sites + 1⟩

theorem kernelEntry_true {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) :
    (kernelEntry columns indices coeff).value = true ↔
      ((∑ i : Fin f, coeff.get i • selected columns indices i) = 0 →
        (fun i => coeff.get i) = 0) := by
  simp only [kernelEntry]
  split_ifs with h
  · rw [coeffZero_true]
    exact (imp_iff_right ((rowsZero_true columns indices coeff).mp h)).symm
  · have hz : ¬ (∑ i : Fin f, coeff.get i • selected columns indices i) = 0 :=
      fun hh => h ((rowsZero_true columns indices coeff).mpr hh)
    simp [hz]

/-- Build both binary extensions by reading stored vector entries. -/
def extend {f : ℕ} (bit : F₂) (v : Vector F₂ f) : Vector F₂ (f+1) :=
  Vector.ofFn (Fin.cons bit v.get)

/-- Joint lexicographic enumeration. Each child is an actual stored vector;
construction charges its field reads/writes, allocation, and list sites. -/
def coefficientsCounted : (f : ℕ) → Result (List (Vector F₂ f))
  | 0 => ⟨[Vector.ofFn (fun i => Fin.elim0 i)], 2⟩
  | f+1 =>
    let prior := coefficientsCounted f
    let zeros := prior.value.map (extend 0)
    let ones := prior.value.map (extend 1)
    ⟨zeros ++ ones, prior.sites + (8*(f+1)+10)*prior.value.length+1⟩

def coefficients (f : ℕ) : List (Vector F₂ f) := (coefficientsCounted f).value

theorem coefficients_eq (f : ℕ) : coefficients f =
    (GoodSetConstruction.binaryColumns f).map (fun c => Vector.ofFn c) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    change (coefficients f).map (extend 0) ++ (coefficients f).map (extend 1) = _
    rw [ih]
    have hget (x : Fin f → F₂) : (Vector.ofFn x).get = x := by
      funext i
      exact Vector.get_ofFn x i
    simp [GoodSetConstruction.binaryColumns, List.map_map, extend, Function.comp_def, hget]

theorem coefficients_length (f : ℕ) : (coefficients f).length = 2^f := by
  rw [coefficients_eq]
  simp

theorem mem_coefficients (f : ℕ) (c : Vector F₂ f) : c ∈ coefficients f := by
  rw [coefficients_eq]
  apply List.mem_map.mpr
  exact ⟨c.get, GoodSetConstruction.mem_binaryColumns f c.get, by apply Vector.ext; intro i hi; rw [Vector.getElem_ofFn]; rfl⟩

theorem coefficientsCounted_sites (f : ℕ) :
    (coefficientsCounted f).sites ≤ 24*(f+1)*2^f := by
  induction f with
  | zero => norm_num [coefficientsCounted]
  | succ f ih =>
    have hl : (coefficientsCounted f).value.length=2^f := coefficients_length f
    simp only [coefficientsCounted, hl, pow_succ]
    have hp : 0 < (2:ℕ)^f := by positivity
    nlinarith

/-- Enumerate all coefficient vectors once, then execute every kernel test. -/
def kernelTest {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f) : Result Bool :=
  let vectors := coefficientsCounted f
  let result := allLoop (kernelEntry columns indices) vectors.value
  ⟨result.value, result.sites + vectors.sites⟩

theorem kernelTest_correct {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f) :
    (kernelTest columns indices).value = true ↔ LinearIndependent F₂ (selected columns indices) := by
  rw [GoodSets.independent_iff_zero_test]
  simp only [kernelTest, allLoop_true, kernelEntry_true]
  constructor
  · intro h c hc
    have hh := h (Vector.ofFn c) (mem_coefficients f (Vector.ofFn c))
    simpa only [Vector.get_ofFn] using hh (by simpa only [Vector.get_ofFn] using hc)
  · intro h c _ hc
    exact h (fun i => c.get i) hc

theorem kernelEntry_sites {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f)
    (coeff : Vector F₂ f) :
    (kernelEntry columns indices coeff).sites ≤ r*(8*f+3)+3*f+3 := by
  have hr := allLoop_sites (fun row : Fin r =>
      let sum := dotLoop columns indices coeff row (List.ofFn (id : Fin f → Fin f))
      (⟨decide (sum.value=0),sum.sites+1⟩ : Result Bool))
    (List.ofFn (id : Fin r → Fin r)) (8*f+2) (by intro row _; simp [dotLoop_sites])
  have hc := allLoop_sites (fun i : Fin f => (⟨decide (coeff.get i=0),2⟩ : Result Bool))
    (List.ofFn (id : Fin f → Fin f)) 2 (by intros; simp)
  simp only [List.length_ofFn] at hr hc
  change (rowsZero columns indices coeff).sites ≤ r*(8*f+2+1)+1 at hr
  change (coeffZero coeff).sites ≤ f*(2+1)+1 at hc
  change (rowsZero columns indices coeff).sites + (coeffZero coeff).sites + 1 ≤ _
  nlinarith

theorem kernelTest_sites {L r f : ℕ} (columns : Columns L r) (indices : Vector (Fin L) f) :
    (kernelTest columns indices).sites ≤ (r*(8*f+3)+27*f+28)*2^f+1 := by
  have h := allLoop_sites (kernelEntry columns indices) (coefficients f)
    (r*(8*f+3)+3*f+3) (fun c _ => kernelEntry_sites columns indices c)
  simp only [coefficients_length] at h
  have he := coefficientsCounted_sites f
  change (allLoop (kernelEntry columns indices) (coefficients f)).sites +
    (coefficientsCounted f).sites ≤ _
  nlinarith

end Kernel

namespace Indexing

open GoodSets

abbrev Columns (L r : ℕ) := Vector (Vector F₂ r) L

def decodeColumns {L r : ℕ} (columns : Columns L r) : BinaryMap r L :=
  fun i j => (columns.get i).get j

def indexSet {L f : ℕ} (indices : Vector (Fin L) f) : Finset (Fin L) :=
  Finset.univ.image indices.get

theorem indexSet_card {L f : ℕ} (indices : Vector (Fin L) f)
    (hi : Function.Injective indices.get) : (indexSet indices).card=f := by
  rw [indexSet, Finset.card_image_of_injective _ hi]
  simp

noncomputable def indexEquiv {L f : ℕ} (indices : Vector (Fin L) f)
    (hi : Function.Injective indices.get) : Fin f ≃ ↥(indexSet indices) :=
  Equiv.ofBijective (fun j => ⟨indices.get j,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩)
    ⟨fun a b hab => hi (congrArg Subtype.val hab), fun q => by
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp q.property
      exact ⟨j,Subtype.ext hj⟩⟩

@[simp] theorem indexEquiv_val {L f : ℕ} (indices : Vector (Fin L) f)
    (hi : Function.Injective indices.get) (j : Fin f) :
    (indexEquiv indices hi j).val=indices.get j := rfl

theorem restrictionTest_indices {L r f : ℕ} (columns : Columns L r)
    (indices : Vector (Fin L) f) (hi : Function.Injective indices.get) :
    GoodSetConstruction.restrictionTest (decodeColumns columns) (indexSet indices)=true ↔
      LinearIndependent F₂ (fun j : Fin f => fun k : Fin r => (columns.get (indices.get j)).get k) := by
  rw [GoodSetConstruction.restrictionTest_correct]
  have h := (linearIndependent_equiv (R := F₂) (indexEquiv indices hi)
    (f := fun q : ↥(indexSet indices) => decodeColumns columns q.val)).symm
  have heq : (fun q : ↥(indexSet indices) => decodeColumns columns q.val) ∘
      (indexEquiv indices hi) =
      (fun j : Fin f => fun k : Fin r => (columns.get (indices.get j)).get k) := by
    funext j k
    change (columns.get (indexEquiv indices hi j).val).get k = _
    rw [indexEquiv_val]
  rw [heq] at h
  exact h

end Indexing

/-- Canonical physical index array, materialized before the kernel loop. -/
def indexList {L : ℕ} (Q : Finset (Fin L)) : List (Fin L) :=
  (List.finRange L).filter (fun i => decide (i ∈ Q))

def indices {L : ℕ} (Q : Finset (Fin L)) : Vector (Fin L) (indexList Q).length :=
  Vector.ofFn (indexList Q).get

theorem indexList_nodup {L : ℕ} (Q : Finset (Fin L)) : (indexList Q).Nodup :=
  (List.nodup_finRange L).filter _

theorem indices_injective {L : ℕ} (Q : Finset (Fin L)) : Function.Injective (indices Q).get := by
  intro a b hab
  apply (indexList_nodup Q).injective_get
  simpa only [indices,Vector.get_ofFn] using hab

theorem indices_set {L : ℕ} (Q : Finset (Fin L)) : Indexing.indexSet (indices Q) = Q := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hi
    have hm : (indexList Q).get j ∈ indexList Q := List.get_mem _ _
    simpa only [indices,Vector.get_ofFn] using
      (show (indices Q).get j ∈ Q from by
        rw [indices,Vector.get_ofFn]
        exact (List.mem_filter.mp hm).2 |> of_decide_eq_true) |> fun h => hj ▸ h
  · intro hi
    have hm : i ∈ indexList Q := by simp [indexList,hi]
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by simpa [indices] using hj⟩

theorem indexList_length {L : ℕ} (Q : Finset (Fin L)) : (indexList Q).length = Q.card := by
  have he : (indexList Q).toFinset = Q := by ext i; simp [indexList]
  rw [←List.toFinset_card_of_nodup (indexList_nodup Q),he]

/-- Executable restriction test on stored arrays with a fully charged
coefficient-vector enumeration, refining the old semantic predicate. -/
def restrictionBits {L r : ℕ} (columns : Kernel.Columns L r) (Q : Finset (Fin L)) : Kernel.Result Bool :=
  let test := Kernel.kernelTest columns (indices Q)
  ⟨test.value,test.sites+4*(L+1)^3⟩

theorem restrictionBits_correct {L r : ℕ} (columns : Kernel.Columns L r) (Q : Finset (Fin L)) :
    (restrictionBits columns Q).value = restrictionTest (Indexing.decodeColumns columns) Q := by
  apply Bool.eq_iff_iff.mpr
  simp only [restrictionBits,Kernel.kernelTest_correct]
  have h := Indexing.restrictionTest_indices columns (indices Q) (indices_injective Q)
  rw [indices_set] at h
  exact h.symm

theorem restrictionBits_sites {L r : ℕ} (columns : Kernel.Columns L r)
    (Q : Finset (Fin L)) (hr : r ≤ L) :
    (restrictionBits columns Q).sites ≤
      (L*(8*L+3)+27*L+33+4*(L+1)^3)*2^L := by
  have hker := Kernel.kernelTest_sites columns (indices Q)
  have hf : (indexList Q).length ≤ L := by
    rw [indexList_length]
    simpa using Finset.card_le_univ Q
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hf
  have hpoly : r*(8*(indexList Q).length+3)+27*(indexList Q).length+28 ≤
      L*(8*L+3)+27*L+28 := by nlinarith
  have hp := Nat.mul_le_mul hpoly hpow
  have hpos : 1 ≤ 2^L := by
    have h : 0 < 2^L := by positivity
    omega
  have hov := Nat.mul_le_mul_left (4*(L+1)^3) hpos
  simp only [restrictionBits]
  nlinarith

namespace Candidates

open scoped BigOperators
open GoodSets Kernel

/-- Decode a stored binary mask by its one-valued cells. -/
def maskSet {L : ℕ} (mask : Vector F₂ L) : Finset (Fin L) :=
  Finset.univ.filter (fun i => mask.get i = 1)

/-- The inverse stored mask for a finite subset. -/
def encodeSet {L : ℕ} (s : Finset (Fin L)) : Vector F₂ L :=
  Vector.ofFn (fun i => if i ∈ s then 1 else 0)

theorem maskSet_encodeSet {L : ℕ} (s : Finset (Fin L)) : maskSet (encodeSet s) = s := by
  ext i
  simp [maskSet, encodeSet]

theorem binary_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem encodeSet_maskSet {L : ℕ} (mask : Vector F₂ L) : encodeSet (maskSet mask) = mask := by
  apply Vector.ext
  intro i hi
  change (encodeSet (maskSet mask)).get ⟨i,hi⟩ = mask.get ⟨i,hi⟩
  rw [encodeSet, Vector.get_ofFn]
  rcases binary_zero_or_one (mask.get ⟨i,hi⟩) with h | h <;> simp [maskSet, h]

theorem maskSet_injective (L : ℕ) : Function.Injective (@maskSet L) := by
  intro a b h
  rw [← encodeSet_maskSet a, ← encodeSet_maskSet b, h]

theorem coefficients_nodup (L : ℕ) : (coefficients L).Nodup := by
  rw [coefficients_eq]
  apply (GoodSetConstruction.binaryColumns_nodup L).map
  intro a b h
  funext i
  have hi := congrArg (fun v : Vector F₂ L => v.get i) h
  simpa only [Vector.get_ofFn] using hi

/-- Retain a mask exactly when its actual decoded set has m elements. -/
def selectCandidate {L : ℕ} (m : ℕ) (mask : Vector F₂ L) : Option (Candidate L m) :=
  let s := maskSet mask
  if h : s.card = m then
    some ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, h⟩⟩
  else none

/-- Concrete enumeration: direct stored binary vectors followed by filterMap. -/
def candidates (L m : ℕ) : List (Candidate L m) :=
  (coefficients L).filterMap (selectCandidate m)

theorem selectCandidate_value {L m : ℕ} (mask : Vector F₂ L) (q : Candidate L m)
    (h : q ∈ selectCandidate m mask) : q.val = maskSet mask := by
  dsimp only [selectCandidate] at h
  split_ifs at h with hc
  · have he : (⟨maskSet mask, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩⟩ : Candidate L m) = q :=
      Option.mem_some_iff.mp h
    exact (congrArg Subtype.val he).symm
  · simp at h

theorem candidates_nodup (L m : ℕ) : (candidates L m).Nodup := by
  unfold candidates
  apply List.Nodup.filterMap _ (coefficients_nodup L)
  intro a b q ha hb
  apply maskSet_injective L
  exact (selectCandidate_value a q ha).symm.trans (selectCandidate_value b q hb)

theorem mem_candidates (L m : ℕ) (q : Candidate L m) : q ∈ candidates L m := by
  have hq : q.val.card = m := (Finset.mem_powersetCard.mp q.property).2
  apply List.mem_filterMap.mpr
  refine ⟨encodeSet q.val, mem_coefficients L _, ?_⟩
  simp only [selectCandidate, maskSet_encodeSet, hq, dif_pos]

theorem candidates_toFinset (L m : ℕ) : (candidates L m).toFinset = Finset.univ := by
  ext q
  simp [mem_candidates]

theorem candidates_length (L m : ℕ) : (candidates L m).length = Nat.choose L m := by
  have hc := GoodSets.candidate_card L m
  rw [Nat.card_eq_fintype_card] at hc
  calc
    (candidates L m).length = (candidates L m).toFinset.card :=
      (List.toFinset_card_of_nodup (candidates_nodup L m)).symm
    _ = Fintype.card (Candidate L m) := by rw [candidates_toFinset]; simp
    _ = Nat.choose L m := hc

/-- The executable enumeration can replace the candidate-type finite sum. -/
theorem sum_map_candidates {M : Type*} [AddCommMonoid M] (L m : ℕ) (f : Candidate L m → M) :
    ((candidates L m).map f).sum = ∑ q : Candidate L m, f q := by
  rw [← candidates_toFinset L m]
  exact (List.sum_toFinset _ (candidates_nodup L m)).symm

end Candidates

def zeroBits : SignedBits := ⟨false,[]⟩
@[simp] theorem zeroBits_value : signedValue zeroBits = 0 := rfl

def clearedNumeratorBits (r f : ℕ) : Kernel.Result SignedBits :=
  let answer := numeratorBits r f (r-f)
  ⟨answer.1,answer.2+2⟩

theorem clearedNumeratorBits_value (r f : ℕ) (hf : f ≤ r) :
    signedValue (clearedNumeratorBits r f).value = (integerNumerator r f : ℤ) := by
  unfold clearedNumeratorBits
  dsimp only
  rw [numeratorBits_value r f (r-f) (by omega)]
  simp only [partialNumerator,integerNumerator,Nat.add_sub_of_le hf]

theorem clearedNumeratorBits_length (r f : ℕ) (hf : f ≤ r) :
    (clearedNumeratorBits r f).value.magnitude.length ≤ r*r+1 :=
  numeratorBits_length r f (r-f) (by omega)

def numeratorBudget (L : ℕ) : ℕ := L*256*(L*L+L+4)^2+L*L+3

theorem clearedNumeratorBits_work (L r f : ℕ) (hr : r ≤ L) (hf : f ≤ r) :
    (clearedNumeratorBits r f).sites ≤ numeratorBudget L := by
  have h := numeratorBits_work r f (r-f) (by omega)
  have hrf : r*f ≤ L*L := Nat.mul_le_mul hr (by omega)
  have hbase : r*r+r+4 ≤ L*L+L+4 := by nlinarith
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_right 256 (show r-f ≤ L by omega))
    (Nat.pow_le_pow_left hbase 2)
  simp only [clearedNumeratorBits,numeratorBudget]
  omega

def kernelPolynomial (L : ℕ) : ℕ := L*(8*L+3)+27*L+33+4*(L+1)^3

def potentialPolynomial (L : ℕ) : ℕ := kernelPolynomial L+numeratorBudget L+4*(L+1)^3+4

/-- All rational arithmetic has disappeared from this potential evaluator. -/
def potentialBits {L r : ℕ} (columns : Kernel.Columns L r) (Q : Finset (Fin L)) (ell : ℕ) :
    Kernel.Result SignedBits :=
  let frame := prefixSet Q ell
  let test := restrictionBits columns frame
  if test.value then
    let number := clearedNumeratorBits r frame.card
    ⟨number.value,test.sites+number.sites+4*(L+1)^3+3⟩
  else ⟨zeroBits,test.sites+4*(L+1)^3+3⟩

theorem potentialBits_value {L r : ℕ} (columns : Kernel.Columns L r)
    (Q : Finset (Fin L)) (hQ : Q.card = r) (ell : ℕ) :
    signedValue (potentialBits columns Q ell).value =
      (integerPotential (Indexing.decodeColumns columns) Q ell : ℤ) := by
  have hf : (prefixSet Q ell).card ≤ r := by
    rw [←hQ]
    exact Finset.card_le_card (prefixSet_subset Q ell)
  simp only [potentialBits,restrictionBits_correct,integerPotential]
  split
  · exact clearedNumeratorBits_value r _ hf
  · rfl

theorem potentialBits_length {L r : ℕ} (columns : Kernel.Columns L r)
    (Q : Finset (Fin L)) (hQ : Q.card = r) (ell : ℕ) (hr : r ≤ L) :
    (potentialBits columns Q ell).value.magnitude.length ≤ L*L+1 := by
  have hf : (prefixSet Q ell).card ≤ r := by
    rw [←hQ]
    exact Finset.card_le_card (prefixSet_subset Q ell)
  unfold potentialBits
  dsimp only
  split
  · exact (clearedNumeratorBits_length r _ hf).trans (by nlinarith)
  · simp [zeroBits]

theorem potentialBits_work {L r : ℕ} (columns : Kernel.Columns L r)
    (Q : Finset (Fin L)) (hQ : Q.card = r) (ell : ℕ) (hr : r ≤ L) :
    (potentialBits columns Q ell).sites ≤ potentialPolynomial L*2^L := by
  have hf : (prefixSet Q ell).card ≤ r := by
    rw [←hQ]
    exact Finset.card_le_card (prefixSet_subset Q ell)
  have hker := restrictionBits_sites columns (prefixSet Q ell) hr
  have hnum := clearedNumeratorBits_work L r _ hr hf
  have hpos : 1 ≤ 2^L := by
    have h : 0 < 2^L := by positivity
    omega
  have ho := Nat.mul_le_mul_left (numeratorBudget L+4*(L+1)^3+3) hpos
  unfold potentialBits
  dsimp only
  split <;> dsimp only
  · unfold potentialPolynomial kernelPolynomial
    nlinarith
  · unfold potentialPolynomial kernelPolynomial
    nlinarith

abbrev ScoreEntries (L : ℕ) := List (Finset (Fin L) × Bool)

def listIntegerScore {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ) (entries : ScoreEntries L) : ℕ :=
  (entries.map (fun entry => if entry.2 then integerPotential (Indexing.decodeColumns columns) entry.1 ell else 0)).sum

/-- Stored bit scores are accumulated by actual normalized bit addition. -/
def scoreBits {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ) : ScoreEntries L → Kernel.Result SignedBits
  | [] => ⟨zeroBits,1⟩
  | entry::rest =>
      let head := if entry.2 then potentialBits columns entry.1 ell else ⟨zeroBits,1⟩
      let tail := scoreBits columns ell rest
      let total := normalizedAddCounted head.value tail.value
      ⟨total.1,head.sites+tail.sites+total.2+4⟩

theorem scoreBits_value {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ entry ∈ entries, entry.1.card = r) :
    (scoreBits columns ell entries).value = ofInt (listIntegerScore columns ell entries : ℤ) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have ht := ih (fun a ha => hs a (by simp [ha]))
      have he := hs entry (by simp)
      unfold scoreBits
      dsimp only
      rw [normalizedAddCounted_value,ht,ofInt_correct]
      cases hw : entry.2
      · simp [hw,zeroBits_value,listIntegerScore]
      · rw [if_pos rfl,potentialBits_value columns entry.1 he ell]
        simp [listIntegerScore,hw]

theorem listIntegerScore_bound {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ entry ∈ entries, entry.1.card = r) :
    listIntegerScore columns ell entries ≤ entries.length*2^(r*r) := by
  unfold listIntegerScore
  calc
    _ ≤ (entries.map (fun _ => 2^(r*r))).sum := by
      apply List.sum_le_sum
      intro entry he
      split
      · unfold integerPotential
        split
        · exact integerNumerator_le r _ (by
            rw [←hs entry he]
            exact Finset.card_le_card (prefixSet_subset entry.1 ell))
        · exact Nat.zero_le _
      · exact Nat.zero_le _
    _ = _ := by simp

def scoreWidth (L : ℕ) : ℕ := L*L+L+1

theorem scoreBits_length {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ entry ∈ entries, entry.1.card = r)
    (hr : r ≤ L) (he : entries.length ≤ 2^L) :
    (scoreBits columns ell entries).value.magnitude.length ≤ scoreWidth L := by
  rw [scoreBits_value columns ell entries hs,ofInt_length,Int.natAbs_natCast]
  apply Nat.size_le.mpr
  have hb := listIntegerScore_bound columns ell entries hs
  have hr2 : r*r ≤ L*L := Nat.mul_le_mul hr hr
  have hp := Nat.mul_le_mul he (Nat.pow_le_pow_right (n := 2) (by decide) hr2)
  have hstrict : 2^(L+L*L) < 2^(L+L*L+1) := by
    rw [pow_succ]
    have h : 0 < 2^(L+L*L) := by positivity
    omega
  rw [←pow_add] at hp
  have h := lt_of_le_of_lt (hb.trans hp) hstrict
  simpa only [scoreWidth,Nat.add_comm L (L*L)] using h

namespace Argmax

open IntegerArithmetic

abbrev Entry (A : Type*) := A × SignedBits

def project {A : Type*} (e : Entry A) : A × ℕ := (e.1, value e.2.magnitude)
def Nonnegative {A : Type*} (e : Entry A) : Prop := e.2.negative = false

structure Result (A : Type*) where
  entry : Entry A
  bitSteps : ℕ

/-- Compare only the already stored magnitude bits. The subtraction's borrow
is true exactly for a strict improvement, so equal scores retain the first. -/
def bitMaxFrom {A : Type*} (best : Entry A) : List (Entry A) → Result A
  | [] => ⟨best, 1⟩
  | entry :: rest =>
    let comparison := subCounted best.2.magnitude entry.2.magnitude false
    let child := bitMaxFrom (if comparison.1.2 then entry else best) rest
    ⟨child.entry, comparison.2 + child.bitSteps + 3⟩

/-- A cached-record maximum: no scoring function occurs in the program. -/
def bitMax {A : Type*} (fallback : Entry A) : List (Entry A) → Result A
  | [] => ⟨fallback, 1⟩
  | best :: rest =>
    let child := bitMaxFrom best rest
    ⟨child.entry, child.bitSteps + 1⟩

theorem borrow_iff {A : Type*} (best entry : Entry A) :
    (subCounted best.2.magnitude entry.2.magnitude false).1.2 = true ↔
      value best.2.magnitude < value entry.2.magnitude := by
  rw [(subCounted_projections _ _ _).1]
  exact subBits_borrow _ _

theorem bitMaxFrom_project {A : Type*} (best : Entry A) (entries : List (Entry A)) :
    project (bitMaxFrom best entries).entry = integerMaxFrom (project best) (entries.map project) := by
  induction entries generalizing best with
  | nil => rfl
  | cons entry rest ih =>
    by_cases hlt : value best.2.magnitude < value entry.2.magnitude
    · have hc := (borrow_iff best entry).mpr hlt
      simp only [bitMaxFrom, hc, ite_true, List.map_cons]
      rw [ih]
      simp only [integerMaxFrom, project, hlt, ite_true]
    · have hc : (subCounted best.2.magnitude entry.2.magnitude false).1.2 = false := by
        cases hb : (subCounted best.2.magnitude entry.2.magnitude false).1.2 with
        | false => rfl
        | true => exact (hlt ((borrow_iff best entry).mp hb)).elim
      simp only [bitMaxFrom, hc, Bool.false_eq_true, ite_false, List.map_cons]
      rw [ih]
      simp only [integerMaxFrom, project, hlt, ite_false]

theorem bitMax_project {A : Type*} (fallback : Entry A) (entries : List (Entry A)) :
    project (bitMax fallback entries).entry = integerMax (project fallback) (entries.map project) := by
  cases entries with
  | nil => rfl
  | cons best rest => exact bitMaxFrom_project best rest

theorem comparison_cost {A : Type*} (best entry : Entry A) (B : ℕ)
    (hb : best.2.magnitude.length ≤ B) (he : entry.2.magnitude.length ≤ B) :
    (subCounted best.2.magnitude entry.2.magnitude false).2 ≤ 12*B+1 := by
  rw [(subCounted_projections _ _ _).2, columnSteps_eq]
  omega

theorem bitMaxFrom_cost {A : Type*} (best : Entry A) (entries : List (Entry A)) (B : ℕ)
    (hb : best.2.magnitude.length ≤ B)
    (he : ∀ e ∈ entries, e.2.magnitude.length ≤ B) :
    (bitMaxFrom best entries).bitSteps ≤ entries.length*(12*B+4)+1 := by
  induction entries generalizing best with
  | nil => simp [bitMaxFrom]
  | cons entry rest ih =>
    have hentry := he entry (by simp)
    have hrest : ∀ e ∈ rest, e.2.magnitude.length ≤ B := fun e h => he e (by simp [h])
    have hcompare := comparison_cost best entry B hb hentry
    cases hc : (subCounted best.2.magnitude entry.2.magnitude false).1.2 with
    | false =>
      have hchild := ih best hb hrest
      simp only [bitMaxFrom, hc, Bool.false_eq_true, ite_false, List.length_cons]
      nlinarith
    | true =>
      have hchild := ih entry hentry hrest
      simp only [bitMaxFrom, hc, ite_true, List.length_cons]
      nlinarith

theorem bitMax_cost {A : Type*} (fallback : Entry A) (entries : List (Entry A)) (B : ℕ)
    (_hf : fallback.2.magnitude.length ≤ B)
    (he : ∀ e ∈ entries, e.2.magnitude.length ≤ B) :
    (bitMax fallback entries).bitSteps ≤ (entries.length+1)*(12*B+6) := by
  cases entries with
  | nil => simp [bitMax]
  | cons best rest =>
    have hb := he best (by simp)
    have hr : ∀ e ∈ rest, e.2.magnitude.length ≤ B := fun e h => he e (by simp [h])
    have hc := bitMaxFrom_cost best rest B hb hr
    simp only [bitMax, List.length_cons]
    nlinarith

theorem bitMaxFrom_nonnegative {A : Type*} (best : Entry A) (entries : List (Entry A))
    (hb : Nonnegative best) (he : ∀ e ∈ entries, Nonnegative e) :
    Nonnegative (bitMaxFrom best entries).entry := by
  induction entries generalizing best with
  | nil => exact hb
  | cons entry rest ih =>
    have hr : ∀ e ∈ rest, Nonnegative e := fun e h => he e (by simp [h])
    cases hc : (subCounted best.2.magnitude entry.2.magnitude false).1.2 with
    | false => simpa only [bitMaxFrom, hc, Bool.false_eq_true, ite_false] using ih best hb hr
    | true => simpa only [bitMaxFrom, hc, ite_true] using ih entry (he entry (by simp)) hr

theorem bitMax_nonnegative {A : Type*} (fallback : Entry A) (entries : List (Entry A))
    (hf : Nonnegative fallback) (he : ∀ e ∈ entries, Nonnegative e) :
    Nonnegative (bitMax fallback entries).entry := by
  cases entries with
  | nil => exact hf
  | cons best rest =>
    exact bitMaxFrom_nonnegative best rest (he best (by simp))
      (fun e h => he e (by simp [h]))

end Argmax

def scorePolynomial (L : ℕ) : ℕ := potentialPolynomial L+50*(scoreWidth L+1)+5

theorem scoreBits_work {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ entry ∈ entries, entry.1.card = r)
    (hr : r ≤ L) (he : entries.length ≤ 2^L) :
    (scoreBits columns ell entries).sites ≤
      entries.length*(potentialPolynomial L*2^L+50*(scoreWidth L+1)+4)+1 := by
  induction entries with
  | nil => simp [scoreBits]
  | cons entry rest ih =>
      have hsrest : ∀ a ∈ rest, a.1.card = r := fun a ha => hs a (by simp [ha])
      have hrestlen : rest.length ≤ 2^L := by simp only [List.length_cons] at he; omega
      have htail := ih hsrest hrestlen
      have htailLen := scoreBits_length columns ell rest hsrest hr hrestlen
      have hentry := hs entry (by simp)
      let head : Kernel.Result SignedBits :=
        if entry.2 then potentialBits columns entry.1 ell else ⟨zeroBits,1⟩
      have hheadLen : head.value.magnitude.length ≤ scoreWidth L := by
        dsimp only [head]
        split
        · exact (potentialBits_length columns entry.1 hentry ell hr).trans (by unfold scoreWidth; omega)
        · simp [zeroBits,scoreWidth]
      have hheadWork : head.sites ≤ potentialPolynomial L*2^L := by
        dsimp only [head]
        split
        · exact potentialBits_work columns entry.1 hentry ell hr
        · have hp : 1 ≤ potentialPolynomial L := by unfold potentialPolynomial; omega
          have ht : 1 ≤ 2^L := by
            have h : 0 < 2^L := by positivity
            omega
          nlinarith
      have hadd := normalizedAddCounted_steps head.value (scoreBits columns ell rest).value
      have hmax : max head.value.magnitude.length (scoreBits columns ell rest).value.magnitude.length ≤
          scoreWidth L := max_le hheadLen htailLen
      have hadd' : (normalizedAddCounted head.value (scoreBits columns ell rest).value).2 ≤
          50*(scoreWidth L+1) := hadd.trans (Nat.mul_le_mul_left 50 (by omega))
      change head.sites+(scoreBits columns ell rest).sites+
        (normalizedAddCounted head.value (scoreBits columns ell rest).value).2+4 ≤ _
      simp only [List.length_cons]
      nlinarith

theorem scoreBits_work_uniform {L r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ entry ∈ entries, entry.1.card = r)
    (hr : r ≤ L) (he : entries.length ≤ 2^L) :
    (scoreBits columns ell entries).sites ≤ (scorePolynomial L+1)*4^L := by
  have h := scoreBits_work columns ell entries hs hr he
  have htwo : 1 ≤ 2^L := by
    have h : 0 < 2^L := by positivity
    omega
  have hfour : 1 ≤ 4^L := by
    have h : 0 < 4^L := by positivity
    omega
  have hconst := Nat.mul_le_mul_left (50*(scoreWidth L+1)+4) htwo
  have hunit : potentialPolynomial L*2^L+50*(scoreWidth L+1)+4 ≤ scorePolynomial L*2^L := by
    unfold scorePolynomial
    nlinarith
  have hprod := Nat.mul_le_mul he hunit
  have hsquare : 2^L*(scorePolynomial L*2^L) = scorePolynomial L*4^L := by
    rw [←GoodSetConstruction.binary_square L]
    ring
  rw [hsquare] at hprod
  nlinarith

def candidatePolynomial (L : ℕ) : ℕ := 24*(L+1)+8*(L+1)^3

/-- Binary masks are generated once; the finite cardinality test is a
bounded mask scan. No enumeration of a noncomputable candidate Fintype runs. -/
def candidatesCounted (L m : ℕ) : Kernel.Result (List (Candidate L m)) :=
  let masks := Kernel.coefficientsCounted L
  ⟨masks.value.filterMap (Candidates.selectCandidate m),
    masks.sites+masks.value.length*(8*(L+1)^3)⟩

@[simp] theorem candidatesCounted_value (L m : ℕ) :
    (candidatesCounted L m).value = Candidates.candidates L m := rfl

theorem candidatesCounted_sites (L m : ℕ) :
    (candidatesCounted L m).sites ≤ candidatePolynomial L*2^L := by
  have h := Kernel.coefficientsCounted_sites L
  have he : (Kernel.coefficientsCounted L).value.length = 2^L := Kernel.coefficients_length L
  simp only [candidatesCounted,he,candidatePolynomial]
  nlinarith

theorem candidates_length_le (L m : ℕ) : (Candidates.candidates L m).length ≤ 2^L := by
  unfold Candidates.candidates
  exact (List.length_filterMap_le _ _).trans_eq (Kernel.coefficients_length L)

def gammaEntries {L m : ℕ} (qs : List (Candidate L m)) : ScoreEntries L :=
  qs.map (fun Q : Candidate L m => (Q.val,true))

/-- Gamma is captured once. Each genuine Gamma weight is stored as a
Boolean beside the already materialized complement before the Delta pass. -/
def deltaEntries {L m : ℕ} (gamma : Kernel.Columns L m) (qs : List (Candidate L m)) :
    Kernel.Result (ScoreEntries L) :=
  let records := qs.map (fun Q : Candidate L m =>
    let tested := restrictionBits gamma Q.val
    (((Q:Finset (Fin L))ᶜ,tested.value),tested.sites+4*(L+1)^3+2))
  ⟨records.map Prod.fst,(records.map Prod.snd).sum⟩

theorem deltaEntries_value {L m : ℕ} (gamma : Kernel.Columns L m) (qs : List (Candidate L m)) :
    (deltaEntries gamma qs).value = qs.map (fun Q : Candidate L m =>
      (Q.valᶜ,restrictionTest (Indexing.decodeColumns gamma) Q.val)) := by
  simp [deltaEntries,List.map_map,Function.comp_def,restrictionBits_correct]

def deltaPolynomial (L : ℕ) : ℕ := kernelPolynomial L+4*(L+1)^3+2

theorem deltaEntries_sites {L m : ℕ} (gamma : Kernel.Columns L m)
    (hm : m ≤ L) :
    (deltaEntries gamma (Candidates.candidates L m)).sites ≤ deltaPolynomial L*4^L := by
  have hlen := candidates_length_le L m
  have htwo : 1 ≤ 2^L := by
    have h : 0 < 2^L := by positivity
    omega
  have hpoint (Q : Candidate L m) :
      (restrictionBits gamma Q).sites+4*(L+1)^3+2 ≤ deltaPolynomial L*2^L := by
    have h := restrictionBits_sites gamma (Q:Finset (Fin L)) hm
    have hc := Nat.mul_le_mul_left (4*(L+1)^3+2) htwo
    unfold deltaPolynomial kernelPolynomial
    nlinarith
  unfold deltaEntries
  simp only [List.map_map,Function.comp_def]
  calc
    _ ≤ ((Candidates.candidates L m).map (fun _ => deltaPolynomial L*2^L)).sum :=
      List.sum_le_sum (fun Q _ => hpoint Q)
    _ = (Candidates.candidates L m).length*(deltaPolynomial L*2^L) := by simp
    _ ≤ 2^L*(deltaPolynomial L*2^L) := Nat.mul_le_mul_right _ hlen
    _ = deltaPolynomial L*4^L := by
      rw [←GoodSetConstruction.binary_square L]
      ring

/-- This setup allowance is absorbed by the explicitly formed raw source
family. It is separate from the finer Gaussian-elimination worksite ledger. -/
theorem setup_source_base (L m : ℕ) : 8^L ≤ 12^L*2^(L-m) := by
  have hbase : 8^L ≤ 12^L := Nat.pow_le_pow_left (by decide) L
  have hpow : 1 ≤ 2^(L-m) := by
    have h : 0 < 2^(L-m) := by positivity
    omega
  exact hbase.trans (by simpa using Nat.mul_le_mul_left (12^L) hpow)

namespace Helpers

open scoped BigOperators

def scoreEntries {L m : ℕ} (sets : Candidate L m → Finset (Fin L))
    (weights : Candidate L m → Bool) : ScoreEntries L :=
  (Candidates.candidates L m).map (fun Q => (sets Q,weights Q))

theorem scoreEntries_card {L m r : ℕ} (sets : Candidate L m → Finset (Fin L))
    (weights : Candidate L m → Bool) (hsets : ∀ Q, (sets Q).card=r) :
    ∀ entry ∈ scoreEntries sets weights, entry.1.card=r := by
  intro entry he
  obtain ⟨Q,_,rfl⟩ := List.mem_map.mp he
  exact hsets Q

theorem listIntegerScore_eq {L m r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (sets : Candidate L m → Finset (Fin L)) (weights : Candidate L m → Bool) :
    listIntegerScore columns ell (scoreEntries sets weights) =
      integerScore sets weights (Indexing.decodeColumns columns) ell := by
  unfold listIntegerScore scoreEntries integerScore
  rw [List.map_map]
  exact Candidates.sum_map_candidates L m _

theorem scoreBits_nat_value {L m r : ℕ} (columns : Kernel.Columns L r) (ell : ℕ)
    (sets : Candidate L m → Finset (Fin L)) (weights : Candidate L m → Bool)
    (hsets : ∀ Q, (sets Q).card=r) :
    value (scoreBits columns ell (scoreEntries sets weights)).value.magnitude =
      integerScore sets weights (Indexing.decodeColumns columns) ell := by
  rw [scoreBits_value columns ell _ (scoreEntries_card sets weights hsets)]
  simp only [ofInt,value_bits,Int.natAbs_natCast]
  exact listIntegerScore_eq columns ell sets weights

def mapPayload {A B : Type*} (f : A → B) (entry : A × ℕ) : B × ℕ :=
  (f entry.1,entry.2)

theorem integerMaxFrom_mapPayload {A B : Type*} (f : A → B)
    (best : A × ℕ) (entries : List (A × ℕ)) :
    integerMaxFrom (mapPayload f best) (entries.map (mapPayload f)) =
      mapPayload f (integerMaxFrom best entries) := by
  induction entries generalizing best with
  | nil => rfl
  | cons entry rest ih =>
      change integerMaxFrom
        (if best.2<entry.2 then mapPayload f entry else mapPayload f best)
        (rest.map (mapPayload f)) =
        mapPayload f (integerMaxFrom (if best.2<entry.2 then entry else best) rest)
      split_ifs <;> exact ih _

theorem integerMax_mapPayload {A B : Type*} (f : A → B)
    (fallback : A × ℕ) (entries : List (A × ℕ)) :
    integerMax (mapPayload f fallback) (entries.map (mapPayload f)) =
      mapPayload f (integerMax fallback entries) := by
  cases entries with
  | nil => rfl
  | cons best rest => exact integerMaxFrom_mapPayload f best rest

end Helpers

namespace Controller

open scoped BigOperators

abbrev Columns := Kernel.Columns

def zeroColumn (r : ℕ) : Vector F₂ r := Vector.ofFn (fun _ => 0)
def zeroColumns (L r : ℕ) : Columns L r := Vector.ofFn (fun _ => zeroColumn r)

/-- Materialize a complete stored column table after replacing one column. -/
def setColumns {L r : ℕ} (columns : Columns L r) (ell : ℕ) (x : Vector F₂ r) : Columns L r :=
  Vector.ofFn (fun i => if i.val = ell then x else columns.get i)

theorem decode_zeroColumns (L r : ℕ) : Indexing.decodeColumns (zeroColumns L r) = 0 := by
  funext i j
  simp [Indexing.decodeColumns, zeroColumns, zeroColumn]

theorem decode_setColumns {L r : ℕ} (columns : Columns L r) (ell : ℕ) (he : ell < L)
    (x : Vector F₂ r) :
    Indexing.decodeColumns (setColumns columns ell x) =
      Function.update (Indexing.decodeColumns columns) ⟨ell,he⟩ x.get := by
  funext i j
  simp only [Indexing.decodeColumns, setColumns, Vector.get_ofFn]
  by_cases hi : i.val = ell
  · have hi' : i = ⟨ell,he⟩ := Fin.ext hi
    subst i
    simp
  · have hi' : i ≠ ⟨ell,he⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi, hi', Indexing.decodeColumns]

/-- Scalar-cell copies, descriptor writes, and table materialization. -/
def copySites (L r : ℕ) : ℕ := 8*(L+1)*(r+1)

/-- Every candidate score is computed once and stored beside its candidate.
The maximum scan subsequently reads only these records. -/
def cacheVectorScores {L r : ℕ} (columns : Columns L r) (ell : ℕ) (entries : ScoreEntries L) :
    List (Vector F₂ r) → Kernel.Result (List (Argmax.Entry (Vector F₂ r)))
  | [] => ⟨[], 1⟩
  | x :: rest =>
    let candidate := setColumns columns ell x
    let score := scoreBits candidate (ell+1) entries
    let tail := cacheVectorScores columns ell entries rest
    ⟨(x,score.value)::tail.value, score.sites+tail.sites+copySites L r+r+3⟩

theorem cacheVectorScores_value {L r : ℕ} (columns : Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (xs : List (Vector F₂ r)) :
    (cacheVectorScores columns ell entries xs).value =
      xs.map (fun x => (x,(scoreBits (setColumns columns ell x) (ell+1) entries).value)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cacheVectorScores, ih]

theorem cacheVectorScores_sites {L r : ℕ} (columns : Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (xs : List (Vector F₂ r)) :
    (cacheVectorScores columns ell entries xs).sites =
      (xs.map (fun x => (scoreBits (setColumns columns ell x) (ell+1) entries).sites +
        copySites L r+r+3)).sum+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cacheVectorScores, ih]; omega

/-- All actual vector candidates, scored once, then selected by bit comparison. -/
def vectorColumnStep {L r : ℕ} (columns : Columns L r) (ell : ℕ) (entries : ScoreEntries L) :
    Kernel.Result (Columns L r) :=
  if ell < L then
    let vectors := Kernel.coefficientsCounted r
    let cached := cacheVectorScores columns ell entries vectors.value
    let maximum := Argmax.bitMax (zeroColumn r,zeroBits) cached.value
    ⟨setColumns columns ell maximum.entry.1,
      vectors.sites+cached.sites+maximum.bitSteps+copySites L r+(ell+1).size+1⟩
  else ⟨columns,(ell+1).size+1⟩

/-- Build the stored column table, preserving all candidate/score/compare work. -/
def vectorBuild {L r : ℕ} (entries : ScoreEntries L) : ℕ → Kernel.Result (Columns L r)
  | 0 => ⟨zeroColumns L r,copySites L r⟩
  | ell+1 =>
    let previous := vectorBuild entries ell
    let next := vectorColumnStep previous.value ell entries
    ⟨next.value,previous.sites+next.sites+(ell+1).size+1⟩


theorem cached_max_get {L m r : ℕ} (columns : Columns L r) (ell : ℕ) (he : ell < L)
    (sets : Candidate L m → Finset (Fin L)) (weights : Candidate L m → Bool)
    (hsets : ∀ Q, (sets Q).card = r) :
    (Argmax.bitMax (zeroColumn r,zeroBits)
      (cacheVectorScores columns ell (Helpers.scoreEntries sets weights) (Kernel.coefficients r)).value).entry.1.get =
      integerSelectColumn r (fun x => integerScore sets weights
        (Function.update (Indexing.decodeColumns columns) ⟨ell,he⟩ x) (ell+1)) := by
  let sc : (Fin r → F₂) → ℕ := fun x => integerScore sets weights
    (Function.update (Indexing.decodeColumns columns) ⟨ell,he⟩ x) (ell+1)
  let cached := cacheVectorScores columns ell (Helpers.scoreEntries sets weights) (Kernel.coefficients r)
  have hrecords : cached.value.map Argmax.project =
      (Kernel.coefficients r).map (fun x => (x,sc x.get)) := by
    rw [cacheVectorScores_value]
    simp only [List.map_map]
    apply List.map_congr_left
    intro x _
    change (x,value (scoreBits (setColumns columns ell x) (ell+1)
      (Helpers.scoreEntries sets weights)).value.magnitude) = (x,sc x.get)
    apply Prod.ext
    · rfl
    have hv := Helpers.scoreBits_nat_value (setColumns columns ell x) (ell+1) sets weights hsets
    simpa only [decode_setColumns columns ell he x, sc] using hv
  have hmax := Argmax.bitMax_project (zeroColumn r,zeroBits) cached.value
  rw [hrecords] at hmax
  have hdecode := congrArg (fun e : Vector F₂ r × ℕ => e.1.get) hmax
  have hnatural := Helpers.integerMax_mapPayload (fun x : Vector F₂ r => x.get)
    (zeroColumn r,0) ((Kernel.coefficients r).map (fun x => (x,sc x.get)))
  have hlist : (((Kernel.coefficients r).map (fun x => (x,sc x.get))).map
      (Helpers.mapPayload (fun x : Vector F₂ r => x.get))) =
      (binaryColumns r).map (fun x => (x,sc x)) := by
    rw [Kernel.coefficients_eq]
    have hget (x : Fin r → F₂) : (Vector.ofFn x).get = x := by
      funext i
      exact Vector.get_ofFn x i
    simp only [List.map_map]
    apply List.map_congr_left
    intro x _
    change ((Vector.ofFn x).get, sc (Vector.ofFn x).get) = (x,sc x)
    rw [hget]
  have hfallback : Helpers.mapPayload (fun x : Vector F₂ r => x.get) (zeroColumn r,0) =
      ((0 : Fin r → F₂),0) := by
    simp only [Helpers.mapPayload, zeroColumn]
    congr 1
    funext i
    exact Vector.get_ofFn _ i
  rw [hlist,hfallback] at hnatural
  have hn := congrArg Prod.fst hnatural
  change (integerMax (0,0) ((binaryColumns r).map (fun x => (x,sc x)))).1 =
    (integerMax (Argmax.project (zeroColumn r,zeroBits))
      ((Kernel.coefficients r).map (fun x => (x,sc x.get)))).1.get at hn
  change (Argmax.bitMax (zeroColumn r,zeroBits) cached.value).entry.1.get =
    (integerMax (Argmax.project (zeroColumn r,zeroBits))
      ((Kernel.coefficients r).map (fun x => (x,sc x.get)))).1.get at hdecode
  exact hdecode.trans hn.symm

theorem vectorColumnStep_value {L m r : ℕ} (columns : Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (sets : Candidate L m → Finset (Fin L))
    (weights : Candidate L m → Bool) (hsets : ∀ Q, (sets Q).card = r)
    (hentries : entries = Helpers.scoreEntries sets weights) :
    Indexing.decodeColumns (vectorColumnStep columns ell entries).value =
      integerColumnStep sets weights ell (Indexing.decodeColumns columns) := by
  subst entries
  by_cases he : ell < L
  · simp only [vectorColumnStep, integerColumnStep, if_pos he, dif_pos he]
    rw [decode_setColumns _ _ he]
    have hc := cached_max_get columns ell he sets weights hsets
    exact congrArg (Function.update (Indexing.decodeColumns columns) ⟨ell,he⟩) hc
  · simp only [vectorColumnStep, integerColumnStep, if_neg he, dif_neg he]

theorem vectorBuild_value {L m r : ℕ} (entries : ScoreEntries L)
    (sets : Candidate L m → Finset (Fin L)) (weights : Candidate L m → Bool)
    (hsets : ∀ Q, (sets Q).card = r) (hentries : entries = Helpers.scoreEntries sets weights) (n : ℕ) :
    Indexing.decodeColumns (vectorBuild (r := r) entries n).value =
      integerBuildMap sets weights n := by
  induction n with
  | zero => exact decode_zeroColumns L r
  | succ n ih =>
    simp only [vectorBuild, integerBuildMap]
    rw [vectorColumnStep_value _ _ _ sets weights hsets hentries, ih]

/-- A deliberately loose polynomial; the exponential factor stays 8^L. -/
def columnPolynomial (L : ℕ) : ℕ :=
  24*(L+1)+(scorePolynomial L+1)+2*(copySites L L+L+4)+2*(12*scoreWidth L+6)+4

theorem cacheVectorScores_cost {L r : ℕ} (columns : Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ e ∈ entries, e.1.card = r)
    (hr : r ≤ L) (he : entries.length ≤ 2^L) (xs : List (Vector F₂ r)) :
    (cacheVectorScores columns ell entries xs).sites ≤
      xs.length*((scorePolynomial L+1)*4^L+copySites L L+L+3)+1 := by
  rw [cacheVectorScores_sites]
  have hcopy : copySites L r ≤ copySites L L := by unfold copySites; gcongr
  have hsum : (xs.map (fun x => (scoreBits (setColumns columns ell x) (ell+1) entries).sites+
      copySites L r+r+3)).sum ≤
      (xs.map (fun _ => (scorePolynomial L+1)*4^L+copySites L L+L+3)).sum := by
    apply List.sum_le_sum
    intro x _
    have hscore := scoreBits_work_uniform (setColumns columns ell x) (ell+1) entries hs hr he
    omega
  simpa using Nat.add_le_add_right hsum 1

theorem vectorColumnStep_sites {L r : ℕ} (columns : Columns L r) (ell : ℕ)
    (entries : ScoreEntries L) (hs : ∀ e ∈ entries, e.1.card = r)
    (hr : r ≤ L) (he : entries.length ≤ 2^L) (hell : ell < L) :
    (vectorColumnStep columns ell entries).sites ≤ columnPolynomial L*8^L := by
  let xs := Kernel.coefficients r
  let cached := cacheVectorScores columns ell entries xs
  let maximum := Argmax.bitMax (zeroColumn r,zeroBits) cached.value
  have h2r : 2^r ≤ 2^L := Nat.pow_le_pow_right (by decide) hr
  have h28 : 2^L ≤ 8^L := Nat.pow_le_pow_left (by decide) L
  have h1 : 1 ≤ (8:ℕ)^L := Nat.one_le_pow _ _ (by decide)
  have h12 : 1 ≤ (2:ℕ)^L := Nat.one_le_two_pow
  have h24 : (2:ℕ)^L*4^L=8^L := by rw [←mul_pow]; norm_num
  have hlen : xs.length = 2^r := Kernel.coefficients_length r
  have hc0 := cacheVectorScores_cost columns ell entries hs hr he xs
  have hc1 : cached.sites ≤ 2^L*((scorePolynomial L+1)*4^L+copySites L L+L+3)+1 := by
    exact hc0.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hlen.trans_le h2r)) 1)
  have hc : cached.sites ≤ ((scorePolynomial L+1)+(copySites L L+L+3)+1)*8^L := by
    have hexpand : 2^L*((scorePolynomial L+1)*4^L+copySites L L+L+3)+1 =
        (scorePolynomial L+1)*8^L+(copySites L L+L+3)*2^L+1 := by rw [←h24]; ring
    rw [hexpand] at hc1
    have hterm := Nat.mul_le_mul_left (copySites L L+L+3) h28
    nlinarith
  have hrecords : ∀ e ∈ cached.value, e.2.magnitude.length ≤ scoreWidth L := by
    intro e hec
    rw [cacheVectorScores_value] at hec
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hec
    exact scoreBits_length (setColumns columns ell x) (ell+1) entries hs hr he
  have hmax0 := Argmax.bitMax_cost (zeroColumn r,zeroBits) cached.value (scoreWidth L)
    (by simp [zeroBits]) hrecords
  have hcachelen : cached.value.length = 2^r := by
    rw [cacheVectorScores_value, List.length_map, hlen]
  have hmax : maximum.bitSteps ≤ 2*(12*scoreWidth L+6)*8^L := by
    rw [hcachelen] at hmax0
    have hlenplus : 2^r+1 ≤ 2*2^L := by omega
    have hm := hmax0.trans (Nat.mul_le_mul_right (12*scoreWidth L+6) hlenplus)
    have hs := Nat.mul_le_mul_left (2*(12*scoreWidth L+6)) h28
    dsimp [maximum]
    nlinarith
  have he0 := Kernel.coefficientsCounted_sites r
  have henum : (Kernel.coefficientsCounted r).sites ≤ 24*(L+1)*8^L := by
    have hm : 24*(r+1)*2^r ≤ 24*(L+1)*2^L := by gcongr
    exact he0.trans (hm.trans (Nat.mul_le_mul_left _ h28))
  have hcopy : copySites L r ≤ copySites L L := by unfold copySites; gcongr
  have hsize : (ell+1).size ≤ L := by
    have ht : (ell+1).size ≤ ell+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hrest : copySites L r+(ell+1).size+1 ≤ (copySites L L+L+1)*8^L := by
    have hscale := Nat.mul_le_mul_left (copySites L L+L+1) h1
    omega
  simp only [vectorColumnStep, if_pos hell]
  change (Kernel.coefficientsCounted r).sites+cached.sites+maximum.bitSteps+
    copySites L r+(ell+1).size+1 ≤ _
  unfold columnPolynomial
  nlinarith

theorem vectorBuild_sites {L r : ℕ} (entries : ScoreEntries L)
    (hs : ∀ e ∈ entries, e.1.card = r) (hr : r ≤ L) (he : entries.length ≤ 2^L)
    (n : ℕ) (hn : n ≤ L) :
    (vectorBuild (r := r) entries n).sites ≤
      copySites L r+n*(columnPolynomial L*8^L+L+2) := by
  induction n with
  | zero => simp [vectorBuild]
  | succ n ih =>
    have hprev := ih (by omega)
    have hstep := vectorColumnStep_sites (vectorBuild (r := r) entries n).value n entries hs hr he (by omega)
    have hsize : (n+1).size ≤ L := by
      have ht : (n+1).size ≤ n+1 := Nat.size_le.mpr Nat.lt_two_pow_self
      omega
    simp only [vectorBuild]
    nlinarith


end Controller

/-- Materialize the good family by original finite kernel checks of both
actual constructed arrays. The two tests are performed once per candidate. -/
def goodFilter {L m : ℕ} (gamma : Kernel.Columns L m) (delta : Kernel.Columns L (L-m)) :
    List (Candidate L m) → Kernel.Result (List (Candidate L m))
  | [] => ⟨[],1⟩
  | Q::rest =>
      let g := restrictionBits gamma Q.val
      let d := restrictionBits delta Q.valᶜ
      let tail := goodFilter gamma delta rest
      ⟨if g.value && d.value then Q::tail.value else tail.value,
        g.sites+d.sites+tail.sites+4*(L+1)^3+5⟩

theorem goodFilter_value {L m : ℕ} (gamma : Kernel.Columns L m) (delta : Kernel.Columns L (L-m))
    (qs : List (Candidate L m)) :
    (goodFilter gamma delta qs).value = qs.filter (fun Q =>
      restrictionTest (Indexing.decodeColumns gamma) Q.val &&
      restrictionTest (Indexing.decodeColumns delta) Q.valᶜ) := by
  induction qs with
  | nil => rfl
  | cons Q qs ih => simp [goodFilter,restrictionBits_correct,ih,List.filter_cons]

theorem goodFilter_mem {L m : ℕ} (gamma : Kernel.Columns L m) (delta : Kernel.Columns L (L-m))
    (qs : List (Candidate L m)) (Q : Candidate L m) :
    Q ∈ (goodFilter gamma delta qs).value ↔ Q ∈ qs ∧
      Good (Indexing.decodeColumns gamma) (Indexing.decodeColumns delta) Q.val := by
  rw [goodFilter_value]
  simp only [List.mem_filter,Bool.and_eq_true,restrictionTest_correct]
  simp only [Good,candidate_size,true_and]

def goodPolynomial (L : ℕ) : ℕ := 2*kernelPolynomial L+4*(L+1)^3+5

theorem goodFilter_sites {L m : ℕ} (gamma : Kernel.Columns L m) (delta : Kernel.Columns L (L-m))
    (hm : m ≤ L) (qs : List (Candidate L m)) :
    (goodFilter gamma delta qs).sites ≤ qs.length*goodPolynomial L*2^L+1 := by
  have htwo : 1 ≤ 2^L := by
    have h : 0 < 2^L := by positivity
    omega
  induction qs with
  | nil => simp [goodFilter]
  | cons Q qs ih =>
      have hg := restrictionBits_sites gamma Q.val hm
      have hd := restrictionBits_sites delta Q.valᶜ (show L-m ≤ L by omega)
      have hc := Nat.mul_le_mul_left (4*(L+1)^3+5) htwo
      simp only [goodFilter,List.length_cons]
      unfold goodPolynomial kernelPolynomial at ih ⊢
      nlinarith

structure Constructed (L m : ℕ) where
  gamma : Kernel.Columns L m
  delta : Kernel.Columns L (L-m)
  good : List (Candidate L m)
  sites : ℕ

/-- Actual deterministic setup. The candidate masks, Gamma table and
Gamma weights are each formed once and captured before the next pass. -/
def construct (L m : ℕ) : Constructed L m :=
  let candidates := candidatesCounted L m
  let gammaData := gammaEntries candidates.value
  let gamma := Controller.vectorBuild (r := m) gammaData L
  let deltaData := deltaEntries gamma.value candidates.value
  let delta := Controller.vectorBuild (r := L-m) deltaData.value L
  let good := goodFilter gamma.value delta.value candidates.value
  ⟨gamma.value,delta.value,good.value,
    candidates.sites+gamma.sites+deltaData.sites+delta.sites+good.sites+
      (candidates.value.length+1)*8*(L+1)^3⟩

def constructedMaps (L m : ℕ) : BinaryMap m L × BinaryMap (L-m) L :=
  let result := construct L m
  (Indexing.decodeColumns result.gamma,Indexing.decodeColumns result.delta)

/-- Exact equality with the old maps includes every strict comparison and
its first-tie rule, rather than merely another pair with sufficient density. -/
theorem constructedMaps_eq (L m : ℕ) : constructedMaps L m = constructGoodMaps L m := by
  let qs := Candidates.candidates L m
  let gdata := gammaEntries qs
  let g := Controller.vectorBuild (r := m) gdata L
  let ddata := deltaEntries g.value qs
  let d := Controller.vectorBuild (r := L-m) ddata.value L
  have hgdata : gdata = Helpers.scoreEntries (fun Q : Candidate L m => Q.val) (fun _ => true) := rfl
  have hg := Controller.vectorBuild_value gdata (fun Q : Candidate L m => Q.val)
    (fun _ => true) candidate_size hgdata L
  have hddata : ddata.value = Helpers.scoreEntries (fun Q : Candidate L m => Q.valᶜ)
      (fun Q => restrictionTest (Indexing.decodeColumns g.value) Q.val) := by
    exact deltaEntries_value g.value qs
  have hd := Controller.vectorBuild_value ddata.value (fun Q : Candidate L m => Q.valᶜ)
    (fun Q => restrictionTest (Indexing.decodeColumns g.value) Q.val) candidate_compl_size hddata L
  change (Indexing.decodeColumns g.value,Indexing.decodeColumns d.value) = constructGoodMaps L m
  rw [←integerConstructGoodMaps_eq]
  unfold integerConstructGoodMaps
  dsimp only
  change Indexing.decodeColumns g.value = _ at hg
  change Indexing.decodeColumns d.value = _ at hd
  rw [hg] at hd
  exact Prod.ext hg hd

theorem constructed_good_value (L m : ℕ) :
    (construct L m).good = (Candidates.candidates L m).filter (fun Q =>
      restrictionTest (constructGoodMaps L m).1 Q.val &&
      restrictionTest (constructGoodMaps L m).2 Q.valᶜ) := by
  have hmaps := constructedMaps_eq L m
  have hg := congrArg Prod.fst hmaps
  have hd := congrArg Prod.snd hmaps
  change Indexing.decodeColumns (construct L m).gamma = _ at hg
  change Indexing.decodeColumns (construct L m).delta = _ at hd
  have hv := goodFilter_value (construct L m).gamma (construct L m).delta (Candidates.candidates L m)
  change (construct L m).good = _ at hv
  rw [hg,hd] at hv
  exact hv

/-- The materialized good-list is exactly the family consumed by the
existing genuine Walsh embedding. -/
theorem constructed_goodSlots (L m : ℕ) :
    ((construct L m).good.map Subtype.val).toFinset = GoodMapEmbedding.goodSlots L m := by
  classical
  ext Q
  rw [GoodMapEmbedding.mem_goodSlots]
  simp only [List.mem_toFinset,List.mem_map,constructed_good_value,List.mem_filter,
    Bool.and_eq_true,restrictionTest_correct]
  constructor
  · rintro ⟨q,⟨_,hq⟩,rfl⟩
    exact ⟨candidate_size q,hq⟩
  · intro hQ
    let q : Candidate L m := ⟨Q,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hQ.1⟩⟩
    exact ⟨q,⟨Candidates.mem_candidates L m q,hQ.2⟩,rfl⟩

theorem constructed_good_nodup (L m : ℕ) : (construct L m).good.Nodup := by
  rw [constructed_good_value]
  exact (Candidates.candidates_nodup L m).filter _

/-- The explicit setup returns the certified dense good family. -/
theorem constructed_good_density (L m : ℕ) :
    Nat.choose L m ≤ 16*(construct L m).good.length := by
  classical
  have h := constructGoodMaps_correct L m
  have he : (construct L m).good.toFinset = Finset.univ.filter (fun Q : Candidate L m =>
      Good (constructGoodMaps L m).1 (constructGoodMaps L m).2 Q.val) := by
    ext Q
    rw [List.mem_toFinset,constructed_good_value]
    simp [Candidates.mem_candidates,Good,candidate_size,restrictionTest_correct]
  rw [←List.toFinset_card_of_nodup (constructed_good_nodup L m),he]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using h

def buildPolynomial (L : ℕ) : ℕ :=
  Controller.copySites L L+L*(Controller.columnPolynomial L+L+2)

theorem vectorBuild_uniform {L r : ℕ} (entries : ScoreEntries L)
    (hs : ∀ e ∈ entries, e.1.card = r) (hr : r ≤ L) (he : entries.length ≤ 2^L) :
    (Controller.vectorBuild (r := r) entries L).sites ≤ buildPolynomial L*8^L := by
  have h := Controller.vectorBuild_sites entries hs hr he L le_rfl
  have hcopy : Controller.copySites L r ≤ Controller.copySites L L := by
    unfold Controller.copySites
    gcongr
  have hpow : 1 ≤ 8^L := Nat.one_le_pow _ _ (by decide)
  have hc := Nat.mul_le_mul_left (Controller.copySites L L+L*(L+2)) hpow
  unfold buildPolynomial
  nlinarith

def constructionPolynomial (L : ℕ) : ℕ :=
  candidatePolynomial L+2*buildPolynomial L+deltaPolynomial L+goodPolynomial L+1+16*(L+1)^3

/-- All setup work belongs to this one program: mask construction, both
stored-column passes, Gamma weight formation and the final good-family scan. -/
theorem construct_sites (L m : ℕ) (hm : m ≤ L) :
    (construct L m).sites ≤ constructionPolynomial L*8^L := by
  let qs := Candidates.candidates L m
  let gdata := gammaEntries qs
  let g := Controller.vectorBuild (r := m) gdata L
  let ddata := deltaEntries g.value qs
  let d := Controller.vectorBuild (r := L-m) ddata.value L
  have hlen : qs.length ≤ 2^L := candidates_length_le L m
  have hgsets : ∀ e ∈ gdata, e.1.card = m := by
    intro e he
    obtain ⟨Q,_,rfl⟩ := List.mem_map.mp he
    exact candidate_size Q
  have hglength : gdata.length ≤ 2^L := by simpa [gdata,gammaEntries] using hlen
  have hdsets : ∀ e ∈ ddata.value, e.1.card = L-m := by
    intro e he
    rw [show ddata.value = _ from deltaEntries_value g.value qs] at he
    obtain ⟨Q,_,rfl⟩ := List.mem_map.mp he
    exact candidate_compl_size Q
  have hdlength : ddata.value.length ≤ 2^L := by
    rw [show ddata.value = _ from deltaEntries_value g.value qs,List.length_map]
    exact hlen
  have hg := vectorBuild_uniform gdata hgsets hm hglength
  have hd := vectorBuild_uniform ddata.value hdsets (show L-m ≤ L by omega) hdlength
  have hc0 := candidatesCounted_sites L m
  have hw0 := deltaEntries_sites g.value hm
  have hgood := goodFilter_sites g.value d.value hm qs
  have h2 : 2^L ≤ 8^L := Nat.pow_le_pow_left (by decide) L
  have h4 : 4^L ≤ 8^L := Nat.pow_le_pow_left (by decide) L
  have h1 : 1 ≤ 8^L := Nat.one_le_pow _ _ (by decide)
  have hc := hc0.trans (Nat.mul_le_mul_left (candidatePolynomial L) h2)
  have hw := hw0.trans (Nat.mul_le_mul_left (deltaPolynomial L) h4)
  have hgoodprod : qs.length*goodPolynomial L*2^L ≤ goodPolynomial L*4^L := by
    calc
      _ ≤ 2^L*goodPolynomial L*2^L :=
        Nat.mul_le_mul_right (2^L) (Nat.mul_le_mul_right (goodPolynomial L) hlen)
      _ = _ := by rw [←GoodSetConstruction.binary_square L]; ring
  have hgood' : (goodFilter g.value d.value qs).sites ≤ (goodPolynomial L+1)*8^L := by
    have hscale := Nat.mul_le_mul_left (goodPolynomial L) h4
    nlinarith
  have hmeta : (qs.length+1)*8*(L+1)^3 ≤ 16*(L+1)^3*8^L := by
    have ht : 1 ≤ 2^L := Nat.one_le_two_pow
    have hl : qs.length+1 ≤ 2*2^L := by omega
    have hp := Nat.mul_le_mul_right (8*(L+1)^3) hl
    have hs := Nat.mul_le_mul_left (16*(L+1)^3) h2
    nlinarith
  change (candidatesCounted L m).sites+g.sites+ddata.sites+d.sites+
    (goodFilter g.value d.value qs).sites+(qs.length+1)*8*(L+1)^3 ≤ _
  unfold constructionPolynomial
  nlinarith

/-- A completely explicit polynomial for the faithful finite bit/setup
instruction model. No rational-arithmetic primitive remains in its program. -/
theorem constructionPolynomial_bound (L : ℕ) :
    constructionPolynomial L ≤ 20241*(L+1)^6 := by
  have hpow (j : ℕ) (hj : j ≤ 6) : L^j ≤ (L+1)^6 :=
    (Nat.pow_le_pow_left (Nat.le_succ L) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have he : constructionPolynomial L =
      512*L^6+1024*L^5+4624*L^4+4386*L^3+8738*L^2+766*L+191 := by
    unfold constructionPolynomial buildPolynomial Controller.columnPolynomial Controller.copySites
      candidatePolynomial deltaPolynomial goodPolynomial kernelPolynomial scorePolynomial
      potentialPolynomial numeratorBudget scoreWidth
    unfold kernelPolynomial
    ring
  rw [he]
  nlinarith [hpow 0 (by omega),hpow 1 (by omega),hpow 2 (by omega),hpow 3 (by omega),
    hpow 4 (by omega),hpow 5 (by omega),hpow 6 (by omega)]

/-- Same returned setup arrays and their charged bit/array work, directly
bounded by the already formed source-family allowance. -/
theorem construct_source_budget (L m : ℕ) (hm : m ≤ L) :
    (construct L m).sites ≤ 20241*(L+1)^6*(12^L*2^(L-m)) := by
  exact ((construct_sites L m hm).trans
    (Nat.mul_le_mul_right (8^L) (constructionPolynomial_bound L))).trans
      (Nat.mul_le_mul_left (20241*(L+1)^6) (setup_source_base L m))

/-- Joint semantic and setup-resource statement for the same actual
returned arrays and materialized good list. -/
theorem construct_contract (L m : ℕ) (hm : m ≤ L) :
    let result := construct L m
    (Indexing.decodeColumns result.gamma,Indexing.decodeColumns result.delta) = constructGoodMaps L m ∧
    (result.good.map Subtype.val).toFinset = GoodMapEmbedding.goodSlots L m ∧
    Nat.choose L m ≤ 16*result.good.length ∧
    result.sites ≤ 20241*(L+1)^6*(12^L*2^(L-m)) := by
  exact ⟨constructedMaps_eq L m,constructed_goodSlots L m,
    constructed_good_density L m,construct_source_budget L m hm⟩

/- Actual finite setup executions; the general contract above supplies
correctness and the resource bounds, independently of these examples. -/
#eval let result := construct 2 1
  (result.gamma.toList.map (fun c => c.toList.map ZMod.val),
    result.delta.toList.map (fun c => c.toList.map ZMod.val),result.good.length,result.sites)
#eval let result := construct 0 0
  (result.good.length,result.sites)

#print axioms construct
#print axioms integerNumerator_eq
#print axioms integerConstructGoodMaps_eq
#print axioms numeratorBits_value
#print axioms numeratorBits_work
#print axioms Kernel.kernelTest_correct
#print axioms Kernel.kernelTest_sites
#print axioms scoreBits_value
#print axioms scoreBits_length
#print axioms Argmax.bitMax_project
#print axioms Controller.vectorBuild_value
#print axioms Controller.vectorBuild_sites
#print axioms constructedMaps_eq
#print axioms constructed_goodSlots
#print axioms constructed_good_density
#print axioms constructionPolynomial_bound
#print axioms construct_source_budget
#print axioms construct_contract

end ThinMatrix.GoodMapRuntime
