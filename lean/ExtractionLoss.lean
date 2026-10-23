import Mathlib

set_option autoImplicit false
namespace ThinMatrix.ExtractionLoss
open Filter
open scoped Topology

noncomputable def loss (x : ℝ) : ℝ :=
  2*Real.log (x+1)+Real.log 72+4*Real.sqrt (Real.log 12+x*Real.log 6)

theorem sqrt_linear_eventually (a b δ : ℝ) (ha : 0≤a) (hb : 0≤b) (hd : 0<δ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt (a+b*x)≤δ*x := by
  filter_upwards [eventually_ge_atTop (max 1 ((a+b)/δ^2))] with x hx
  have hx1 : 1≤x := (le_max_left _ _).trans hx
  have hxb : (a+b)/δ^2≤x := (le_max_right _ _).trans hx
  have hh : a+b≤δ^2*x := by
    have := (div_le_iff₀ (sq_pos_of_pos hd)).mp hxb
    nlinarith
  have hh' := mul_le_mul_of_nonneg_right hh (by linarith : 0≤x)
  have hs := Real.sq_sqrt (show 0≤a+b*x by positivity)
  have hp : 0≤δ*x := by positivity
  nlinarith [mul_nonneg ha (show 0≤x-1 by linarith)]

theorem log_shift_eventually (δ : ℝ) (hd : 0<δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (x+1)≤δ*x := by
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.mp
    (Real.isLittleO_log_id_atTop.bound (show 0<δ/2 by positivity))
  filter_upwards [eventually_ge_atTop (max 1 A)] with x hx
  have hx1 : 1≤x := (le_max_left _ _).trans hx
  have hxA : A≤x+1 := by have := (le_max_right _ _).trans hx;linarith
  have h := hA (x+1) hxA
  have h' : |Real.log (x+1)|≤δ/2*(x+1) := by
    simpa only [Real.norm_eq_abs,id_eq,abs_of_nonneg (show 0≤x+1 by linarith)] using h
  calc
    _ ≤ |Real.log (x+1)| := le_abs_self _
    _ ≤ δ/2*(x+1) := h'
    _ ≤ _ := by nlinarith

/-- Every strict linear slack eventually absorbs both finite multinomial
losses, the cleanup constant, and the explicit Behrend square-root loss. -/
theorem eventually_loss_le (ε : ℝ) (he : 0<ε) :
    ∀ᶠ x : ℝ in atTop, loss x≤ε*x := by
  have hl := log_shift_eventually (ε/6) (by positivity)
  have hs := sqrt_linear_eventually (Real.log 12) (Real.log 6) (ε/12)
    (by positivity) (by positivity) (by positivity)
  filter_upwards [hl,hs,eventually_ge_atTop (3*Real.log 72/ε)] with x hl hs hc
  have hc' : 3*Real.log 72≤x*ε := (div_le_iff₀ he).mp hc
  rw [mul_comm (Real.log 6) x] at hs
  unfold loss
  linarith

theorem exp_loss (x a : ℝ) (hx : 0<x+1) :
    Real.exp (a-loss x)=Real.exp a/(x+1)^2/72*
      Real.exp (-4*Real.sqrt (Real.log 12+x*Real.log 6)) := by
  have hd : Real.exp (2*Real.log (x+1)+Real.log 72)=(x+1)^2*72 := by
    rw [show 2*Real.log (x+1)=Real.log (x+1)+Real.log (x+1) by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hx,Real.exp_log (by norm_num : (0:ℝ)<72)]
    ring
  have he : a-loss x=(a-(2*Real.log (x+1)+Real.log 72))+
      (-4*Real.sqrt (Real.log 12+x*Real.log 6)) := by unfold loss;ring
  rw [he,Real.exp_add,Real.exp_sub,hd,div_mul_eq_div_div]

#print axioms exp_loss
#print axioms sqrt_linear_eventually
#print axioms log_shift_eventually
#print axioms eventually_loss_le
end ThinMatrix.ExtractionLoss
