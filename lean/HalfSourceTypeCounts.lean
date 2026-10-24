import HalfSourceTypeEntropy
import HalfSourceSuffixFeasible

/-! Connect the global entropy envelope to the actual rounded suffix
selector and finite channel-type binomial multiplicities. -/
namespace ThinMatrix.HalfSourceTypeCounts
open HalfSourceParameters HalfSourceTypeEntropy
open HalfSourceSuffixChoice HalfSourceSuffixFeasible
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem strict_type_fraction (m cn co : ℕ) (hm : 0 < m)
    (ht : cn+co < OptimizedFoldedPlan.channelLength m) :
    (cn:ℝ)/m+(co:ℝ)/m  ≤  2*theta := by
  rw [OptimizedFoldedPlan.channelLength_eq,Nat.lt_ceil] at ht
  have he : OptimizedFoldedPlan.theta=theta := by rfl
  rw [he] at ht
  rw [← add_div]
  apply (div_le_iff₀ (by exact_mod_cast hm : (0:ℝ)< m)).mpr
  exact (show (cn:ℝ)+(co:ℝ)< 2*theta*m by exact_mod_cast ht).le

theorem max_fraction (m cn co : ℕ) : max ((cn:ℝ)/m) ((co:ℝ)/m)=(max cn co:ℕ)/m := by
  rw [max_div_div_right (Nat.cast_nonneg m),Nat.cast_max]

theorem rare_ratio_upper (m cn co : ℕ) (hm : 32  ≤  m)
    (ht : cn+co < OptimizedFoldedPlan.channelLength m) :
    ((m/2-max cn co:ℕ):ℝ)/(OptimizedFoldedPlan.ordinaryLength m-m:ℕ)  ≤
      probability (max ((cn:ℝ)/m) ((co:ℝ)/m)) := by
  let k := OptimizedFoldedPlan.ordinaryLength m-m
  let a : ℝ := max ((cn:ℝ)/m) ((co:ℝ)/m)
  have hm0 : 0 < m := by omega
  have hmR : (0:ℝ)< m := by exact_mod_cast hm0
  have hchannel : max cn co  ≤  OptimizedFoldedPlan.channelLength m := (max_le (by omega) (by omega))
  have hr := rare_quarter m cn co hm hchannel
  have hhalf : max cn co  ≤  m/2 := by omega
  have hfloor : (2:ℝ)*(m/2:ℕ)  ≤  m := by exact_mod_cast (show 2*(m/2) ≤ m by omega)
  have hkR : (0:ℝ)< k := by exact_mod_cast (show 0< k by have := suffix_eight m; dsimp [k]; omega)
  have hk : (c-1)*(m:ℝ)  ≤  (k:ℝ) := by
    have hl := (OptimizedFoldedPlan.rounded_bounds m).1
    have he : OptimizedFoldedPlan.c=c := by norm_num [OptimizedFoldedPlan.c,c]
    rw [he] at hl
    dsimp [k]
    rw [Nat.cast_sub (OptimizedFoldedPlan.ordinaryLength_lower m)]
    linarith
  have ha0 : 0  ≤  a := (div_nonneg (Nat.cast_nonneg cn) hmR.le).trans (le_max_left _ _)
  have hasum := strict_type_fraction m cn co hm0 ht
  have ha1 : a  ≤  2*theta := max_le (by have := div_nonneg (Nat.cast_nonneg co) hmR.le; linarith)
    (by have := div_nonneg (Nat.cast_nonneg cn) hmR.le; linarith)
  have ha : 0  ≤  1/2-a := by linarith [constants.2.1]
  have hnum : ((m/2-max cn co:ℕ):ℝ)  ≤  (m:ℝ)*(1/2-a) := by
    rw [Nat.cast_sub hhalf]
    have hid : (m:ℝ)*(1/2-a)=(m:ℝ)/2-(max cn co:ℕ) := by
      dsimp [a]
      rw [max_fraction]
      field_simp
    rw [hid]
    linarith
  change _  ≤  (1/2-a)/(c-1)
  apply (div_le_div_iff₀ hkR constants.2.2.1).mpr
  have h1 := mul_le_mul_of_nonneg_right hnum constants.2.2.1.le
  have h2 := mul_le_mul_of_nonneg_left hk ha
  nlinarith only [h1,h2]

theorem selected_length_ideal (m cn co : ℕ) (hm : 32  ≤  m)
    (ht : cn+co < OptimizedFoldedPlan.channelLength m) :
    (m:ℝ)*zeta/HalfSourceTypeEntropy.gamma (max ((cn:ℝ)/m) ((co:ℝ)/m))-1 <
      (forType (OptimizedFoldedPlan.ordinaryLength m) m cn co:ℝ) := by
  have hm0 : 0 < m := by omega
  have hchannel : max cn co  ≤  OptimizedFoldedPlan.channelLength m := max_le (by omega) (by omega)
  have hs := selected_length m cn co hm hchannel
  have hp := type_ratio m cn co hm hchannel
  have hsums := strict_type_fraction m cn co hm0 ht
  have hx : (0:ℝ)  ≤  (cn:ℝ)/m := by positivity
  have hy : (0:ℝ)  ≤  (co:ℝ)/m := by positivity
  have ha : max ((cn:ℝ)/m) ((co:ℝ)/m)  ≤  2*theta := max_le (by linarith) (by linarith)
  have hpb := probability_bounds (hx.trans (le_max_left _ _)) ha
  have hH : 0 < Real.binEntropy (((m/2-max cn co:ℕ):ℝ)/(OptimizedFoldedPlan.ordinaryLength m-m:ℕ)) :=
    (quotient_fits m cn co hm hchannel).1
  have hHle := Real.binEntropy_strictMonoOn.monotoneOn
    (show (((m/2-max cn co:ℕ):ℝ)/(OptimizedFoldedPlan.ordinaryLength m-m:ℕ))∈Set.Icc (0:ℝ) (2⁻¹) from
      ⟨hp.1.le,by norm_num at hp ⊢; linarith [hp.2]⟩)
    (show probability (max ((cn:ℝ)/m) ((co:ℝ)/m))∈Set.Icc (0:ℝ) (2⁻¹) from
      ⟨hpb.1.le,by simpa only [one_div] using hpb.2.le⟩)
    (rare_ratio_upper m cn co hm ht)
  have hz0 := constants.2.2.2.1.le
  have hl0 := constants.2.2.2.2.le
  have hq := div_le_div_of_nonneg_left
    (show 0  ≤  (m:ℝ)*zeta*Real.log 4 by positivity) hH hHle
  have he : (m:ℝ)*zeta/HalfSourceTypeEntropy.gamma (max ((cn:ℝ)/m) ((co:ℝ)/m))=
      (m:ℝ)*zeta*Real.log 4/Real.binEntropy (probability (max ((cn:ℝ)/m) ((co:ℝ)/m))) := by
    unfold HalfSourceTypeEntropy.gamma
    field_simp
  rw [he]
  have hz : HalfSourceBatchFit.zeta=zeta := by rfl
  rw [hz] at hs
  exact lt_of_le_of_lt (sub_le_sub_right hq 1) hs

/-- Exact binomial multiplicities and the actual selected suffix length,
including the one-coordinate rounding loss. -/
theorem type_multiplicity_bound (m cn co : ℕ) (hm : 32 ≤ m)
    (ht : cn+co < OptimizedFoldedPlan.channelLength m) :
    (m.choose cn:ℝ)*(m.choose co:ℝ)*(2:ℝ)^(-(forType (OptimizedFoldedPlan.ordinaryLength m) m cn co:ℝ)) ≤
      2*(((4:ℝ)^m)^(Q-zeta/(2*gamt))) := by
  have hm0 : 0 < m := by omega
  have hc := OptimizedFoldedPlan.channelLength_upper m
  have hcn : cn ≤ m := by omega
  have hco : co ≤ m := by omega
  let x : ℝ := (cn:ℝ)/m
  let y : ℝ := (co:ℝ)/m
  let ell := forType (OptimizedFoldedPlan.ordinaryLength m) m cn co
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hs : x+y ≤ 2*theta := strict_type_fraction m cn co hm0 ht
  have htype := type_envelope hx hy hs
  have hlen : (m:ℝ)*zeta/HalfSourceTypeEntropy.gamma (max x y)-1 < (ell:ℝ) := selected_length_ideal m cn co hm ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := constants.2.2.2.2
  have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hg := gamma_positive (hx.trans (le_max_left x y))
    (show max x y ≤ 2*theta from max_le (by linarith) (by linarith))
  have hid : (m:ℝ)*Real.log 4*typeScore x y=
      (m:ℝ)*(Real.binEntropy x+Real.binEntropy y)-
        ((m:ℝ)*zeta/HalfSourceTypeEntropy.gamma (max x y))*Real.log 2 := by
    unfold typeScore
    rw [RealCertificate.logFour]
    field_simp
  have hlenm := mul_lt_mul_of_pos_right hlen hlog2
  have htypeM := mul_le_mul_of_nonneg_left htype (mul_nonneg hmR hlog4.le)
  have hexponent : (m:ℝ)*(Real.binEntropy x+Real.binEntropy y)-(ell:ℝ)*Real.log 2 ≤
      Real.log 2+(m:ℝ)*Real.log 4*(Q-zeta/(2*gamt)) := by
    calc
      _ ≤ Real.log 2+(m:ℝ)*(Real.binEntropy x+Real.binEntropy y)-
          ((m:ℝ)*zeta/HalfSourceTypeEntropy.gamma (max x y))*Real.log 2 := by linarith only [hlenm]
      _ = Real.log 2+(m:ℝ)*Real.log 4*typeScore x y := by rw [hid]; ring
      _ ≤ _ := by linarith only [htypeM]
  have hp : (2:ℝ)^(-(ell:ℝ))=Real.exp (-(ell:ℝ)*Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hd : ((4:ℝ)^m)^(Q-zeta/(2*gamt))=
      Real.exp ((m:ℝ)*Real.log 4*(Q-zeta/(2*gamt))) := by
    rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
  have hb := mul_le_mul (EntropyBounds.choose_entropy_upper_of_le m cn hcn)
    (EntropyBounds.choose_entropy_upper_of_le m co hco) (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hb' := mul_le_mul_of_nonneg_right hb (show 0 ≤ (2:ℝ)^(-(ell:ℝ)) by positivity)
  change _ ≤ 2*(((4:ℝ)^m)^(Q-zeta/(2*gamt)))
  calc
    _ ≤ (Real.exp ((m:ℝ)*Real.binEntropy x)*Real.exp ((m:ℝ)*Real.binEntropy y))*(2:ℝ)^(-(ell:ℝ)) := hb'
    _ = Real.exp ((m:ℝ)*(Real.binEntropy x+Real.binEntropy y)-(ell:ℝ)*Real.log 2) := by
      rw [hp,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log 2+(m:ℝ)*Real.log 4*(Q-zeta/(2*gamt))) := Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),← hd]

def typeMass (m cn co : ℕ) : ℝ := if cn+co < OptimizedFoldedPlan.channelLength m then
    (m.choose cn:ℝ)*(m.choose co:ℝ)*(2:ℝ)^(-(forType (OptimizedFoldedPlan.ordinaryLength m) m cn co:ℝ))
  else 0

theorem typeMass_bound (m cn co : ℕ) (hm : 32 ≤ m) :
    typeMass m cn co ≤ 2*(((4:ℝ)^m)^(Q-zeta/(2*gamt))) := by
  unfold typeMass
  split_ifs with ht
  · exact type_multiplicity_bound m cn co hm ht
  · positivity

/-- Sum every ordered channel type, including the empty type and all
unbalanced types. The only loss is an explicit quadratic factor in m. -/
theorem all_types_bound (m : ℕ) (hm : 32 ≤ m) :
    (∑ cn ∈ Finset.range (m+1), ∑ co ∈ Finset.range (m+1), typeMass m cn co) ≤
      2*(m+1:ℝ)^2*(((4:ℝ)^m)^(Q-zeta/(2*gamt))) := by
  have h := Finset.sum_le_sum (s:=Finset.range (m+1)) fun cn _ =>
    Finset.sum_le_sum (s:=Finset.range (m+1)) fun co _ => typeMass_bound m cn co hm
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at h
  exact h.trans_eq (by ring)

#print axioms type_multiplicity_bound
#print axioms typeMass_bound
#print axioms all_types_bound

#print axioms strict_type_fraction
#print axioms max_fraction
#print axioms rare_ratio_upper
#print axioms selected_length_ideal
end
end ThinMatrix.HalfSourceTypeCounts
