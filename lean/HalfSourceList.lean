import HalfSourceGreedy
import HalfSourceCoverage

set_option autoImplicit false

/-!
# A deterministic rational translation list

Columns are selected by the bitwise algorithm in `HalfSourceGreedy`.
The construction retains list occurrences, including repeated vectors.
No search over complete lists or random oracle is used.
-/

namespace ThinMatrix.HalfSourceList
open ThinMatrix.WalshEmbedding ThinMatrix.HalfSourceGreedy
open scoped BigOperators

abbrev Characters (m : ℕ) := {a : Cube m // a ≠ zeroBits m}

def sign (b : Bool) : ℤ := if b then -1 else 1

def sumSign {m : ℕ} (ds : List (Cube m)) (a : Cube m) : ℤ :=
  (ds.map (fun d => sign (dotBits a d))).sum

def potential {m : ℕ} (r : ℚ) (ds : List (Cube m)) : ℚ :=
  ∑ a : Characters m, (r ^ sumSign ds a.val + r ^ (-sumSign ds a.val))

def next {m : ℕ} (r : ℚ) (ds : List (Cube m)) : Cube m :=
  select r (fun a : Characters m => r ^ sumSign ds a.val)
    (fun a : Characters m => r ^ (-sumSign ds a.val)) m
    (fun a => a.val) (fun _ => false)

def build (m : ℕ) (r : ℚ) : ℕ → List (Cube m)
  | 0 => []
  | j+1 => let ds := build m r j; next r ds :: ds

@[simp] theorem build_length (m : ℕ) (r : ℚ) (j : ℕ) :
    (build m r j).length = j := by
  induction j <;> simp_all [build]

theorem sumSign_cons {m : ℕ} (d : Cube m) (ds : List (Cube m)) (a : Cube m) :
    sumSign (d :: ds) a = sumSign ds a + sign (dotBits a d) := by
  simp [sumSign,add_comm]

theorem tilt_powers (r : ℚ) (hr : r ≠ 0) (s : ℤ) (b : Bool) :
    r^(s+sign b)+r^(-(s+sign b)) = tilt r (r^s) (r^(-s)) b := by
  cases b <;> simp [sign,tilt,zpow_add₀ hr,div_eq_mul_inv,mul_comm]

theorem next_contraction {m : ℕ} (r : ℚ) (hr : r ≠ 0) (ds : List (Cube m)) :
    potential r (next r ds :: ds) ≤ potential r ds * mean r := by
  have h := select_le r (fun a : Characters m => r ^ sumSign ds a.val)
    (fun a : Characters m => r ^ (-sumSign ds a.val)) m
    (fun a => a.val) (fun _ => false)
  rw [expectation_nonzero r _ _ _ (fun a => a.property)] at h
  simpa only [potential,sumSign_cons,tilt_powers r hr,terminalSigns,
    Bool.false_xor,next] using h

theorem characters_card (m : ℕ) : Fintype.card (Characters m) = 2^m-1 := by
  simp [Characters,Fintype.card_subtype_compl]

theorem empty_potential (m : ℕ) (r : ℚ) :
    potential (m := m) r [] = 2*((2:ℚ)^m-1) := by
  have hp : 1 ≤ 2^m := Nat.one_le_pow m 2 (by decide)
  simp [potential,sumSign,Nat.cast_sub hp]
  ring

theorem build_potential (m : ℕ) (r : ℚ) (hr : 0 < r) (j : ℕ) :
    potential r (build m r j) ≤ 2*((2:ℚ)^m-1)*(mean r)^j := by
  induction j with
  | zero => simp [build,empty_potential]
  | succ j ih =>
      have hm : 0 ≤ mean r := by unfold mean; positivity
      calc
        _ ≤ potential r (build m r j)*mean r := next_contraction r (ne_of_gt hr) _
        _ ≤ (2*((2:ℚ)^m-1)*(mean r)^j)*mean r := mul_le_mul_of_nonneg_right ih hm
        _ = _ := by rw [pow_succ]; ring

def rationalBase (m : ℕ) : ℚ := 1 + 1/(4*(m:ℚ))
def translations (m : ℕ) : List (Cube m) :=
  build m (rationalBase m) (HalfSourcePotential.listLength m)

@[simp] theorem translations_length (m : ℕ) :
    (translations m).length = 64*m^3 := build_length _ _ _

theorem rationalBase_gt_one (m : ℕ) (hm : 0 < m) : 1 < rationalBase m := by
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  unfold rationalBase
  linarith [show (0:ℚ) < 1/(4*(m:ℚ)) by positivity]

theorem uniform_threshold (m : ℕ) (hm : 0 < m) :
    2*((2:ℚ)^m-1)*(mean (rationalBase m))^(64*m^3) <
      rationalBase m ^ (32*m^2) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hr : (0:ℝ) < HalfSourcePotential.base m := by
    unfold HalfSourcePotential.base HalfSourcePotential.step
    positivity
  have hc : 0 < HalfSourcePotential.meanFactor m := by
    unfold HalfSourcePotential.meanFactor
    positivity
  have hcount : 0 < 2*((2:ℝ)^m-1) := by
    have h := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : m ≠ 0)
    linarith
  have h := HalfSourcePotential.uniform_initial_gap m hm
  have hscale : (HalfSourcePotential.listLength m:ℝ)*HalfSourcePotential.bias m =
      (32*m^2:ℕ) := by
    simp only [HalfSourcePotential.listLength,HalfSourcePotential.bias,
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    field_simp
    ring
  have hex : 2*((2:ℝ)^m-1)*HalfSourcePotential.meanFactor m^(64*m^3) <
      HalfSourcePotential.base m^(32*m^2) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (ne_of_gt hcount) (by positivity), Real.log_pow, Real.log_pow]
    have he : (HalfSourcePotential.listLength m:ℝ)*
        (HalfSourcePotential.bias m*Real.log (HalfSourcePotential.base m)-
          Real.log (HalfSourcePotential.meanFactor m)) =
        ((32*m^2:ℕ):ℝ)*Real.log (HalfSourcePotential.base m)-
          ((64*m^3:ℕ):ℝ)*Real.log (HalfSourcePotential.meanFactor m) := by
      rw [mul_sub,← mul_assoc,hscale]
      rfl
    rw [he] at h
    linarith
  have hbase : (rationalBase m:ℝ) = HalfSourcePotential.base m := by
    simp [rationalBase,HalfSourcePotential.base,HalfSourcePotential.step]
  have hmean : (mean (rationalBase m):ℝ) = HalfSourcePotential.meanFactor m := by
    simp [mean,HalfSourcePotential.meanFactor,hbase]
  exact_mod_cast (show 2*((2:ℝ)^m-1)*(mean (rationalBase m):ℝ)^(64*m^3) <
      (rationalBase m:ℝ)^(32*m^2) by rw [hmean,hbase]; exact hex)

theorem translations_potential_lt (m : ℕ) (hm : 0 < m) :
    potential (rationalBase m) (translations m) < rationalBase m^(32*m^2) :=
  (build_potential m (rationalBase m) (lt_trans (by norm_num) (rationalBase_gt_one m hm))
    (64*m^3)).trans_lt (uniform_threshold m hm)

theorem translations_sign_bound (m : ℕ) (hm : 0 < m) (a : Characters m) :
    |sumSign (translations m) a.val| < (32*m^2:ℕ) := by
  let r := rationalBase m
  let s := sumSign (translations m) a.val
  have hr1 : 1 < r := rationalBase_gt_one m hm
  have hr : 0 < r := lt_trans (by norm_num) hr1
  have hterm : r^s+r^(-s) ≤ potential r (translations m) := by
    change r^(sumSign (translations m) a.val)+r^(-sumSign (translations m) a.val) ≤
      ∑ b : Characters m, (r^(sumSign (translations m) b.val)+r^(-sumSign (translations m) b.val))
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun b : Characters m => r^(sumSign (translations m) b.val)+r^(-sumSign (translations m) b.val))
      (fun b _ => by positivity) (Finset.mem_univ a)
  have hp := translations_potential_lt m hm
  have hs : r^s < r^(32*m^2) := lt_of_le_of_lt (by linarith [zpow_pos hr (-s)]) (hterm.trans_lt hp)
  have hn : r^(-s) < r^(32*m^2) := lt_of_le_of_lt (by linarith [zpow_pos hr s]) (hterm.trans_lt hp)
  have hs' : s < (32*m^2:ℕ) := by
    apply (zpow_lt_zpow_iff_right₀ hr1).mp
    rw [zpow_natCast]
    exact hs
  have hn' : -s < (32*m^2:ℕ) := by
    apply (zpow_lt_zpow_iff_right₀ hr1).mp
    rw [zpow_natCast]
    exact hn
  exact abs_lt.mpr ⟨by linarith,hs'⟩

theorem sumSign_get_real {m : ℕ} (ds : List (Cube m)) (a : Cube m) :
    (sumSign ds a:ℝ) = ∑ j : Fin ds.length, character (R := ℝ) a (ds.get j) := by
  have he : ∀ d, (sign (dotBits a d):ℝ) = character (R := ℝ) a d := by
    intro d
    rw [character_eq_sign_dot]
    cases dotBits a d <;> norm_num [sign,bitSign]
  simp only [sumSign,Int.cast_list_sum,List.map_map,Function.comp_def,he]
  conv_lhs => rw [← List.ofFn_get ds,List.map_ofFn,List.sum_ofFn]
  rfl

theorem translations_smallBias (m : ℕ) (hm : 0 < m) :
    HalfSourceCoverage.SmallBias (translations m).get (1/(2*(m:ℝ))) := by
  intro a ha
  have h := translations_sign_bound m hm ⟨a,ha⟩
  have hr : |(sumSign (translations m) a:ℝ)| < ((32*m^2:ℕ):ℝ) := by exact_mod_cast h
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [sumSign_get_real] at hr
  have he : ((translations m).length:ℝ)*(1/(2*(m:ℝ))) = ((32*m^2:ℕ):ℝ) := by
    rw [translations_length]
    push_cast
    field_simp
    ring
  simpa only [he] using hr

/-- The concrete rational list covers every affine translate under every
binary row map with nonzero rows. The list has exactly 64 m^3 entries. -/
theorem translations_half_coverage (m : ℕ) (hm : 0 < m)
    (rows : Fin m → Cube m) (hr : ∀ i, rows i ≠ zeroBits m) (h : Cube m) :
    ∃ j : Fin (translations m).length,
      ones (HalfSourceCoverage.rowMap rows (xorBits h ((translations m).get j))) ≤ m/2 := by
  have hJ : 0 < (translations m).length := by rw [translations_length]; positivity
  exact HalfSourceCoverage.affine_half_coverage hm hJ _ (translations_smallBias m hm) rows hr h

#print axioms build_length
#print axioms sumSign_cons
#print axioms tilt_powers
#print axioms next_contraction
#print axioms characters_card
#print axioms empty_potential
#print axioms build_potential
#print axioms translations_length
#print axioms rationalBase_gt_one
#print axioms uniform_threshold
#print axioms translations_potential_lt
#print axioms translations_sign_bound
#print axioms sumSign_get_real
#print axioms translations_smallBias
#print axioms translations_half_coverage

end ThinMatrix.HalfSourceList
