import BinaryAPSPHostStages
import ArithmeticSlack
import ComputableParameters

/-!
# Complete binary APSP host allowance from the original graph

These bounds require an original polynomial edge bound. They apply to every
binary triangle callback, including incorrect callbacks: digit refinement
itself bounds the host accumulator. The returned oracle work is separate.
Original graph encoding and all public host constants and controls are
included in `run.hostBits`.
-/
namespace ThinMatrix.BinaryAPSPHostTotalCosts
open BinaryAPSPCaller BinaryAPSPHostCosts BinaryAPSPHostStages
open AdaptiveQueryBitBounds
open Filter Asymptotics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem budget_eight (n degree : ℕ) : 8 ≤ budget n degree := by
  unfold budget
  omega

theorem original_size_budget (n degree W : ℕ) (hW : W ≤ n^degree) :
    W.size ≤ budget n degree := by
  have hs := original_bound_size n degree W hW
  have hb := (budget_bounds n degree).2
  unfold exponent at hb
  nlinarith only [hs,hb]

theorem graph_bits_budget {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W) (hW : W ≤ n^degree) :
    ∀ i j z, StoredMinPlusAPSP.decode w i j=some z → z.natAbs.size ≤ budget n degree := by
  intro i j z hz
  exact (Nat.size_le_size (hw i j z hz)).trans (original_size_budget n degree W hW)

theorem encoded_graph_fits {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W) (hW : W ≤ n^degree) :
    OptionalFits (4*budget n degree) (encodeGraph w).value := by
  intro i j c hc
  have he := congrArg (fun A => StoredMinPlusAPSP.decode A i j) (encodeGraph_view w)
  rw [viewOptional_get,hc] at he
  have hz : StoredMinPlusAPSP.decode w i j=some (BinaryCell.view c) := he.symm
  have hb := graph_bits_budget w W degree hw hW i j (BinaryCell.view c) hz
  change (BinaryCell.view c).natAbs.size ≤ 4*budget n degree
  omega

theorem host_schedule_budget (n degree W : ℕ) (hW : W ≤ n^degree) :
    2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W))+
        (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)).size+6 ≤ 4*budget n degree ∧
      4*budget n degree+
        2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W))+
        APSPReduction.rounds n+20 ≤ 10*budget n degree := by
  have hb := budget_eight n degree
  have he := (budget_bounds n degree).2
  have hn := (budget_bounds n degree).1
  have hd := bit_depth_bound n degree W hW
  have hs := sentinel_size n degree W hW
  have hr := rounds_bound n
  constructor <;> omega

theorem tablePrice_budget (n degree : ℕ) :
    tablePrice n (10*budget n degree) ≤ 2000000000*(budget n degree)^3 := by
  let B := budget n degree
  have hb : 8 ≤ B := budget_eight n degree
  have hn : n.size+1 ≤ B := (budget_bounds n degree).1
  have hc : (10*B+3)^3 ≤ (11*B)^3 := Nat.pow_le_pow_left (by omega) 3
  have hp : B ≤ B^3 := le_self_pow₀ (by omega) (by decide)
  change scalarPrice (10*B)+8*(n.size+1)+4 ≤ 2000000000*B^3
  unfold scalarPrice
  nlinarith only [hb,hn,hc,hp]

theorem squaring_coefficient_budget (n degree W : ℕ) (hW : W ≤ n^degree) :
    1+APSPReduction.rounds n*
      (6*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W))+11) ≤
        18*(budget n degree)^2 := by
  have hb := budget_eight n degree
  have hr : APSPReduction.rounds n ≤ budget n degree :=
    (rounds_bound n).trans (budget_bounds n degree).1
  have hd : MinPlusReduction.signedLevels
      (APSPAlgorithm.sentinel (APSPAlgorithm.globalBound n W)) ≤ budget n degree :=
    (bit_depth_bound n degree W hW).trans (by have he := (budget_bounds n degree).2; omega)
  have hm := Nat.mul_le_mul hr (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hd) 11)
  nlinarith only [hm,hb]

theorem encodeGraph_budget {n : ℕ} (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W) (hW : W ≤ n^degree) :
    (encodeGraph w).bitSteps ≤ 54*n^2*(budget n degree)^2 := by
  have he := encodeGraph_price w (budget n degree) (graph_bits_budget w W degree hw hW)
  have hb := budget_eight n degree
  have hn := (budget_bounds n degree).1
  have hc : 10*(budget n degree+1)^2+8*(n.size+1)+6 ≤ 54*(budget n degree)^2 := by
    nlinarith only [hb,hn]
  exact he.trans ((Nat.mul_le_mul_left (n^2) hc).trans_eq (by ring))

theorem public_control_budget (n degree W : ℕ) (hn : 0<n) (hW : W ≤ n^degree) :
    32*(n.size+W.size+2)^2 ≤ 288*n^2*(budget n degree)^2 := by
  have hnsize := (budget_bounds n degree).1
  have hWsize := original_size_budget n degree W hW
  have hb := budget_eight n degree
  have hc : n.size+W.size+2 ≤ 3*budget n degree := by omega
  have hp := Nat.pow_le_pow_left hc 2
  have hbound : 32*(n.size+W.size+2)^2 ≤ 288*(budget n degree)^2 := by
    nlinarith only [hp]
  exact hbound.trans ((Nat.le_mul_of_pos_left (288*(budget n degree)^2)
    (show 0<n^2 by positivity)).trans_eq (by ring))

/-- Every host operation is priced from the original graph. No callback
correctness or callback-cost premise occurs in this host theorem. -/
theorem run_hostBits_le {n : ℕ} {Payload : Type} (hn : 0<n) (O : Oracle n Payload)
    (w : StoredMinPlusAPSP.OptionalTable n) (W degree : ℕ)
    (hw : APSPReduction.EdgeBound (StoredMinPlusAPSP.decode w) W) (hW : W ≤ n^degree) :
    (run O w W).hostBits ≤ 40000000000*n^2*(budget n degree)^5 := by
  let B := budget n degree
  let loaded := encodeGraph w
  let core := apsp O loaded.value W
  have hsched := host_schedule_budget n degree W hW
  have hs := squared_hostBits_le hn O loaded.value (APSPAlgorithm.globalBound n W)
    (4*B) (10*B) (APSPReduction.rounds n) (encoded_graph_fits w W degree hw hW)
    hsched.1 hsched.2
  have hc := squaring_coefficient_budget n degree W hW
  have ht := tablePrice_budget n degree
  have hcore : core.hostBits ≤ 36000000000*n^2*B^5 := by
    change core.hostBits ≤ _ at hs
    apply hs.trans
    calc
      _ ≤ (18*B^2)*n^2*(2000000000*B^3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) ht
      _ = _ := by ring
  have he : loaded.bitSteps ≤ 54*n^2*B^2 := encodeGraph_budget w W degree hw hW
  have hcontrol : 32*(n.size+W.size+2)^2 ≤ 288*n^2*B^2 := public_control_budget n degree W hn hW
  have hB : 1 ≤ B := (by have hb := budget_eight n degree; dsimp only [B]; omega)
  have hp : B^2 ≤ B^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hrest : 342*n^2*B^2 ≤ 342*n^2*B^5 := Nat.mul_le_mul_left _ hp
  change core.hostBits+loaded.bitSteps+32*(n.size+W.size+2)^2 ≤ _
  nlinarith only [hcore,he,hcontrol,hrest]

noncomputable def hostAllowance (degree n : ℕ) : ℝ :=
  40000000000*(n : ℝ)^2*(budget n degree : ℝ)^5

theorem budget_le_log (n degree : ℕ) (hn : 3 ≤ n) :
    (budget n degree : ℝ) ≤ ((5*(degree+1)+8 : ℕ) : ℝ)*Real.log (n : ℝ) := by
  have hs := ComputableParameters.size_le_four_log n hn
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hsize : (n.size : ℝ)+1 ≤ 5*Real.log (n : ℝ) := by linarith only [hs,hl]
  have hm := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ (degree+1 : ℕ) from Nat.cast_nonneg _)
  calc
    (budget n degree : ℝ) = ((degree+1 : ℕ) : ℝ)*((n.size : ℝ)+1)+8 := by
      simp only [budget,Nat.cast_add,Nat.cast_mul,Nat.cast_one, Nat.cast_ofNat]
    _ ≤ ((degree+1 : ℕ) : ℝ)*(5*Real.log (n : ℝ))+8*Real.log (n : ℝ) := by linarith only [hm,hl]
    _ = _ := by push_cast; ring

theorem hostAllowance_bigO (degree : ℕ) :
    hostAllowance degree =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792/100000000 : ℝ)) := by
  let C : ℝ := ((5*(degree+1)+8 : ℕ) : ℝ)
  let K : ℝ := 40000000000*C^5
  have hlog : (fun n : ℕ => K*(Real.log (n : ℝ))^5*(n : ℝ)^2)
      =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792/100000000 : ℝ)) := by
    have h := (AsymptoticCosts.logPowMulRpowBigO (a:=2)
      (d:=(299294792/100000000 : ℝ)) (by norm_num) 5).const_mul_left K
    simpa only [Real.rpow_two,mul_assoc] using h
  have hdom : hostAllowance degree =O[atTop] (fun n : ℕ => K*(Real.log (n : ℝ))^5*(n : ℝ)^2) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    rw [Real.norm_of_nonneg (show 0 ≤ hostAllowance degree n by unfold hostAllowance; positivity)]
    have hb := budget_le_log n degree hn
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (budget n degree)) hb 5
    change (budget n degree : ℝ)^5 ≤ (C*Real.log (n : ℝ))^5 at hp
    calc
      hostAllowance degree n ≤ 40000000000*(n : ℝ)^2*(C*Real.log (n : ℝ))^5 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = K*(Real.log (n : ℝ))^5*(n : ℝ)^2 := by rw [mul_pow]; dsimp only [K]; ring
  exact hdom.trans hlog

theorem run_hostBits_bigO (Payload : ℕ → Type) (O : (n : ℕ) → Oracle n (Payload n))
    (w : (n : ℕ) → StoredMinPlusAPSP.OptionalTable n) (W : ℕ → ℕ) (degree : ℕ)
    (hw : ∀ n, APSPReduction.EdgeBound (StoredMinPlusAPSP.decode (w n)) (W n))
    (hW : ∀ n, W n ≤ n^degree) :
    (fun n : ℕ => ((run (O n) (w n) (W n)).hostBits : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)^(299294792/100000000 : ℝ)) := by
  have hdom : (fun n : ℕ => ((run (O n) (w n) (W n)).hostBits : ℝ)) =O[atTop] hostAllowance degree := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h := run_hostBits_le (by omega) (O n) (w n) (W n) degree (hw n) (hW n)
    unfold hostAllowance
    exact_mod_cast h
  exact hdom.trans (hostAllowance_bigO degree)

#print axioms encoded_graph_fits
#print axioms host_schedule_budget
#print axioms tablePrice_budget
#print axioms encodeGraph_budget
#print axioms run_hostBits_le
#print axioms budget_le_log
#print axioms hostAllowance_bigO
#print axioms run_hostBits_bigO

end ThinMatrix.BinaryAPSPHostTotalCosts
