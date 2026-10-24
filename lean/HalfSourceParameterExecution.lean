import HalfSourcePrimeParameters
import ParameterExecution

/-! Binary execution of the exact-half prime-parameter selector. All input
serialization, root scans, candidate trial division, finite validation and
metadata decoding use the existing proved bit-list programs. The new
witness is installed into the actual composite configuration. -/
namespace ThinMatrix.HalfSourceParameterExecution
open IntegerArithmetic BackendScalarBits
open ParameterExecution
open HalfSourceBatchFit HalfSourcePrimeParameters
open ComputableParameters (rootScan roundedPower size_le_four_log)
open Filter Asymptotics
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
attribute [local irreducible] ComputableParameters.rootScan Nat.pow HalfSourceBatchFit.block HalfSourceBatchFit.scale

def prepare (n U : ℕ) : Run Data :=
  prepareWith bNumerator bDenominator R n U

def Correct (n U : ℕ) (d : Data) : Prop :=
  d.block.view=HalfSourceBatchFit.block n ∧
  d.scale.view=HalfSourceBatchFit.scale n ∧ d.lam.view=U.size ∧
  d.reserve.view=HalfSourcePrimeParameters.reserve n ∧ d.stages.view=(2*n).size ∧
  (d.pool.map Word.view).toFinset=computedPool n ∧ (d.pool.map Word.view).Nodup

theorem prepare_correct (n U : ℕ) : Correct n U (prepare n U).value := by
  have h := prepareWith_correct bNumerator bDenominator R n U
  simpa only [prepare,Correct,Data.CorrectWith,HalfSourceBatchFit.block,
    HalfSourceBatchFit.scale,roundedPower,HalfSourcePrimeParameters.reserve,computedPool] using h
attribute [irreducible] prepare

def validate (d : Data) : Run Bool :=
  let scale := less (input 1) d.scale
  let positive := less (input 0) d.reserve
  let twice := mul (input 2) d.lam
  let half := less d.reserve twice.value
  let lambdaPower := power d.lam R
  let fourBlock := mul (input 4) d.block
  let numerator := mul fourBlock.value lambdaPower.value
  let denominator := power d.reserve R
  let rate := less denominator.value numerator.value
  ⟨scale.value && positive.value && !half.value && !rate.value,
    scale.bitSteps+positive.bitSteps+twice.bitSteps+half.bitSteps+lambdaPower.bitSteps+
    fourBlock.bitSteps+numerator.bitSteps+denominator.bitSteps+rate.bitSteps+3⟩

theorem validate_correct (n U : ℕ) (d : Data) (hd : Correct n U d) :
    (validate d).value = true ↔ Good n U := by
  have hl : ∀ x y : Word, (less x y).value = false ↔ y.view ≤ x.view := by
    intro x y
    rw [Bool.eq_false_iff]
    exact not_congr (less_view x y) |>.trans not_lt
  simp only [validate,Bool.and_eq_true,Bool.not_eq_true',less_view,input_view,
    mul_view,power_view,hl,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1]
  unfold Good
  omega
attribute [irreducible] validate

def prepareEncoded (n U : ℕ) : Run Data :=
  let nr := serialize n
  let ur := serialize U
  let out := prepareWordsWith bNumerator bDenominator R n U nr.value ur.value
  ⟨out.value,nr.bitSteps+ur.bitSteps+out.bitSteps+1⟩

theorem prepareEncoded_value (n U : ℕ) : (prepareEncoded n U).value=(prepare n U).value := by
  simp only [prepareEncoded,prepareWords_eq _ _ _ _ _ _ _ (serialize_eq_input n) (serialize_eq_input U),prepare]

theorem prepareEncoded_steps (n U : ℕ) : (prepareEncoded n U).bitSteps =
    (BinaryMultiplierAdapter.encodeNat n).bitSteps+(BinaryMultiplierAdapter.encodeNat U).bitSteps+
      (prepare n U).bitSteps+1 := by
  simp only [prepareEncoded,prepareWords_eq _ _ _ _ _ _ _ (serialize_eq_input n) (serialize_eq_input U),prepare]
  rfl

def configurationDecoded (n U : ℕ) (d : Data) (hd : Correct n U d)
    (m : Decoded) (hm : m.Correct d) (h : Good n U) :
    CompleteAPSP.Parameters (HalfSourceBatchFit.block n) U where
  pool := nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2)
  P := m.scale
  lam := m.lam
  k := R-1
  M := m.reserve
  stages := m.stages
  prime := by
    intro p hp
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he] at hp
    exact (finiteComputedParameters n U h).prime p hp
  lower := by
    intro p hp
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he] at hp
    simpa only [hm.2.1,hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).lower p hp
  P_pos := by simpa only [hm.2.1,hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).P_pos
  power := by simpa only [hm.2.1,hm.2.2.1,hd.2.1,hd.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).power
  threshold := by simpa only [hm.2.2.1,hm.2.2.2.1,hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).threshold
  size := by
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he]
    simpa only [hm.2.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).size
  rate := by simpa only [hm.2.2.1,hm.2.2.2.1,hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).rate

theorem configurationDecoded_eq (n U : ℕ) (d : Data) (hd : Correct n U d)
    (m : Decoded) (hm : m.Correct d) (h : Good n U) :
    configurationDecoded n U d hd m hm h = finiteComputedParameters n U h := by
  unfold configurationDecoded finiteComputedParameters
  rw [CompleteAPSP.Parameters.mk.injEq]
  refine ⟨?_,hm.2.1.trans hd.2.1,hm.2.2.1.trans hd.2.2.1,rfl,
    hm.2.2.2.1.trans hd.2.2.2.1,hm.2.2.2.2.1.trans hd.2.2.2.2.1⟩
  ext x
  simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
  rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]

structure Execution (n U : ℕ) where
  value : Option (CompleteAPSP.Parameters (HalfSourceBatchFit.block n) U)
  metadata : Decoded
  bitSteps : ℕ

/-- Input words, all binary setup results, and the decoded public metadata are
retained once. The implementation never calls the reference program. -/
def execute (n U : ℕ) : Execution n U :=
  let prepared := prepareEncoded n U
  have hd : Correct n U prepared.value := prepareEncoded_value n U ▸ prepare_correct n U
  let checked := validate prepared.value
  let metadata := decodeData prepared.value
  if h : checked.value = true then
    ⟨some (configurationDecoded n U prepared.value hd metadata.value (decodeData_correct prepared.value)
      ((validate_correct n U prepared.value hd).mp h)),metadata.value,
      prepared.bitSteps+checked.bitSteps+metadata.bitSteps+1⟩
  else ⟨none,metadata.value,prepared.bitSteps+checked.bitSteps+metadata.bitSteps+1⟩

theorem execute_value (n U : ℕ) : (execute n U).value = program n U := by
  have hd : Correct n U (prepareEncoded n U).value := prepareEncoded_value n U ▸ prepare_correct n U
  by_cases hg : Good n U
  · have hc := (validate_correct n U _ hd).mpr hg
    simp only [execute,hc,dif_pos,program,hg,configurationDecoded_eq]
  · have hc : ¬(validate (prepareEncoded n U).value).value = true :=
      fun h => hg ((validate_correct n U _ hd).mp h)
    simp only [execute,hc,dif_neg,program,hg,Bool.false_eq_true,dif_neg,not_false_eq_true]

theorem execute_steps (n U : ℕ) : (execute n U).bitSteps =
    (prepareEncoded n U).bitSteps+(validate (prepareEncoded n U).value).bitSteps+
      (decodeData (prepareEncoded n U).value).bitSteps+1 := by
  dsimp only [execute]
  split_ifs <;> rfl

theorem execute_metadata (n U : ℕ) : (execute n U).metadata=(decodeData (prepare n U).value).value := by
  dsimp only [execute]
  split_ifs
  all_goals change (decodeData (prepareEncoded n U).value).value = _
  all_goals rw [prepareEncoded_value]

theorem validate_price (B : ℕ) (d : Data) (h8 : (8:ℕ).size ≤ B)
    (hs : d.scale.view.size ≤ B) (hm : d.reserve.view.size ≤ B)
    (hl : d.lam.view.size ≤ B) (hb : d.block.view.size ≤ B)
    (ht : (2*d.lam.view).size ≤ B) (hf : (4*d.block.view).size ≤ B)
    (hn : (4*d.block.view*d.lam.view^R).size ≤ B)
    (hlp : ∀ j ≤ R, (d.lam.view^j).size ≤ B)
    (hmp : ∀ j ≤ R, (d.reserve.view^j).size ≤ B) :
    (validate d).bitSteps ≤ (2*R+12)*(unit B+1) := by
  have hc (z : ℕ) (hz : z ≤ 8) : (input z).view.size ≤ B := by
    rw [input_view]
    exact (Nat.size_le_size hz).trans h8
  have hsc := less_price B (input 1) d.scale (hc 1 (by omega)) hs
  have hpo := less_price B (input 0) d.reserve (hc 0 (by omega)) hm
  have htw := mul_price B (input 2) d.lam (hc 2 (by omega)) hl
  have hha := less_price B d.reserve (mul (input 2) d.lam).value hm
    (by rw [mul_view,input_view];exact ht)
  have hlpow := power_price B d.lam R hl hlp
  have hfour := mul_price B (input 4) d.block (hc 4 (by omega)) hb
  have hnum := mul_price B (mul (input 4) d.block).value (power d.lam R).value
    (by rw [mul_view,input_view];exact hf) (by rw [power_view];exact hlp _ le_rfl)
  have hden := power_price B d.reserve R hm hmp
  have hra := less_price B (power d.reserve R).value
    (mul (mul (input 4) d.block).value (power d.lam R).value).value
    (by rw [power_view];exact hmp _ le_rfl)
    (by rw [mul_view,mul_view,input_view,power_view];exact hn)
  simp only [validate]
  nlinarith

lemma scale_width (n : ℕ) : (scale n).size ≤ 5*(n.size+1) := by
  unfold scale
  have hr := (Nat.size_le_size (roundedPower_le bNumerator (bDenominator*R) n)).trans (size_succ n)
  have hp : (n.size^4).size ≤ 4*n.size+1 :=
    (size_pow _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (size_le_self _)) 1)
  exact (size_mul _ _).trans (by nlinarith)
lemma block_width (n : ℕ) : (HalfSourceBatchFit.block n).size ≤ n.size+1 := by
  unfold HalfSourceBatchFit.block
  exact (Nat.size_le_size (roundedPower_le _ _ n)).trans (size_succ n)
lemma reserve_le (n : ℕ) : HalfSourcePrimeParameters.reserve n ≤ 8*scale n :=
  (Nat.sub_le _ _).trans (pool_card_le _)

def registerWidth (n U : ℕ) : ℕ :=
  (bNumerator+bDenominator*R+10*R+100)*(n.size+2)+(R+1)*U.size

lemma validate_registers (n U : ℕ) :
    (validate (prepare n U).value).bitSteps ≤ (2*R+12)*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  let d := (prepare n U).value
  have hd := prepare_correct n U
  have hR : R = 100000000000000 := rfl
  have h8 : (8:ℕ).size ≤ B := by change 4 ≤ B; dsimp [B,registerWidth,bNumerator,bDenominator,R]; omega
  have hsc : (scale n).size ≤ B := (scale_width n).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,R];omega)
  have hres : (HalfSourcePrimeParameters.reserve n).size ≤ 9*(n.size+1) :=
    (Nat.size_le_size (reserve_le n)).trans ((size_eight_mul _).trans (by nlinarith [scale_width n]))
  have hm : (HalfSourcePrimeParameters.reserve n).size ≤ B := hres.trans (by dsimp [B,registerWidth,bNumerator,bDenominator,R];omega)
  have hl : U.size.size ≤ B := (size_le_self _).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,R];nlinarith)
  have hb : (HalfSourceBatchFit.block n).size ≤ B := (block_width n).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,R];omega)
  have hlp : ∀ j ≤ R, (U.size^j).size ≤ B := by
    intro j hj
    have h := size_pow U.size j
    have hs := size_le_self U.size
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    nlinarith
  have hmp : ∀ j ≤ R, (HalfSourcePrimeParameters.reserve n^j).size ≤ B := by
    intro j hj
    have h := size_pow (HalfSourcePrimeParameters.reserve n) j
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    nlinarith
  have ht : (2*U.size).size ≤ B := (size_mul _ _).trans (by
    have h2 : (2:ℕ).size=2 := by decide
    rw [h2];dsimp [B,registerWidth,bNumerator,bDenominator,R];nlinarith [size_le_self U.size])
  have hf : (4*HalfSourceBatchFit.block n).size ≤ B := (size_mul _ _).trans (by
    have h4 : (4:ℕ).size=3 := by decide
    rw [h4];dsimp [B,registerWidth,bNumerator,bDenominator,R];nlinarith [block_width n])
  have hn : (4*HalfSourceBatchFit.block n*U.size^R).size ≤ B := by
    have h1 := size_mul (4*HalfSourceBatchFit.block n) (U.size^R)
    have h2 := size_mul 4 (HalfSourceBatchFit.block n)
    have h3 := size_pow U.size R
    have h4 : (4:ℕ).size=3 := by decide
    rw [h4] at h2
    rw [hR] at h1 h3
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    nlinarith [block_width n,size_le_self U.size]
  apply validate_price B d h8
  all_goals simp only [d,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1]
  · exact hsc
  · exact hm
  · exact hl
  · exact hb
  · exact ht
  · exact hf
  · exact hn
  · exact hlp
  · exact hmp

lemma decodePrepared_price (n U : ℕ) :
    (decodeData (prepare n U).value).bitSteps ≤ (8*scale n+6)*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  let d := (prepare n U).value
  have hd := prepare_correct n U
  have hbound : 9*(n.size+1)+U.size ≤ B := by
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    omega
  have hb : d.block.view.size≤B := by rw [show d.block.view=HalfSourceBatchFit.block n from hd.1]; nlinarith [block_width n]
  have hs : d.scale.view.size≤B := by rw [show d.scale.view=scale n from hd.2.1];nlinarith [scale_width n]
  have hl : d.lam.view.size≤B := by rw [show d.lam.view=U.size from hd.2.2.1];nlinarith [size_le_self U.size]
  have hm : d.reserve.view.size≤B := by
    rw [show d.reserve.view=HalfSourcePrimeParameters.reserve n from hd.2.2.2.1]
    have h := (Nat.size_le_size (reserve_le n)).trans (size_eight_mul (scale n))
    nlinarith [scale_width n]
  have ht : d.stages.view.size≤B := by
    rw [show d.stages.view=(2*n).size from hd.2.2.2.2.1]
    have h := size_mul 2 n
    have h2 : (2:ℕ).size=2 := by decide
    rw [h2] at h
    nlinarith [size_le_self ((2*n).size)]
  have hp : ∀ x∈d.pool,x.view.size≤B := by
    intro x hx
    have hmem : x.view∈computedPool n := by
      rw [←hd.2.2.2.2.2.1]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩)
    have hxle : x.view ≤ 8*scale n := by
      have hmem' := (Finset.mem_sdiff.mp hmem).1
      exact (Finset.mem_range.mp (Finset.mem_filter.mp hmem').1).le
    have h := (Nat.size_le_size hxle).trans (size_eight_mul (scale n))
    nlinarith [scale_width n]
  have hlen : d.pool.length ≤ 8*scale n := by
    rw [←List.length_map (f:=Word.view) (as:=d.pool),←List.toFinset_card_of_nodup hd.2.2.2.2.2.2,
      hd.2.2.2.2.2.1]
    exact pool_card_le _
  exact (decodeData_price B d hb hs hl hm ht hp).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 6))

noncomputable def widthCoefficient (κ : ℝ) : ℝ :=
  6*(bNumerator+bDenominator*R+10*R+100:ℕ)+
    (R+1:ℕ)*(4*(Nat.ceil κ:ℝ)+1)

lemma widthCoefficient_nonneg (κ : ℝ) : 0 ≤ widthCoefficient κ := by
  unfold widthCoefficient
  positivity

lemma registerWidth_le_log (n U : ℕ) (κ : ℝ) (hn : 3≤n)
    (hU : (U:ℝ)≤(n:ℝ)^κ) :
    (registerWidth n U:ℝ) ≤ widthCoefficient κ*Real.log (n:ℝ) := by
  have hs := size_le_four_log n hn
  have hu := input_size_of_real_power n U κ (by omega) hU
  have huR : (U.size:ℝ) ≤ (Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := by exact_mod_cast hu
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hUs : (U.size:ℝ) ≤ (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) := by
    nlinarith [(show (0:ℝ)≤(Nat.ceil κ:ℝ) by positivity)]
  unfold registerWidth widthCoefficient
  push_cast
  have hc : (0:ℝ) ≤ (bNumerator:ℝ)+(bDenominator:ℝ)*R+10*R+100 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (show (n.size:ℝ)+2 ≤ 6*Real.log (n:ℝ) by linarith) hc
  have h2 := mul_le_mul_of_nonneg_left hUs (show (0:ℝ)≤(R:ℝ)+1 by positivity)
  nlinarith

noncomputable def unitCoefficient (κ : ℝ) : ℝ := 1000*(widthCoefficient κ+1)^2+1
lemma unitCoefficient_pos (κ : ℝ) : 0 < unitCoefficient κ := by unfold unitCoefficient;positivity

lemma unit_le_log_square (n U : ℕ) (κ : ℝ) (hn : 3≤n)
    (hU : (U:ℝ)≤(n:ℝ)^κ) :
    (unit (registerWidth n U)+1:ℝ) ≤ unitCoefficient κ*(Real.log (n:ℝ))^2 := by
  have hw := registerWidth_le_log n U κ hn hU
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hc := widthCoefficient_nonneg κ
  have h : (registerWidth n U:ℝ)+1 ≤ (widthCoefficient κ+1)*Real.log (n:ℝ) := by nlinarith
  have hh : ((registerWidth n U:ℝ)+1)^2 ≤ ((widthCoefficient κ+1)*Real.log (n:ℝ))^2 := by gcongr
  unfold unit unitCoefficient
  push_cast
  nlinarith [sq_nonneg (Real.log (n:ℝ)-1)]

lemma eventually_scale_le_n : ∀ᶠ n : ℕ in atTop, scale n ≤ n := by
  have h := AsymptoticCosts.eventualPowerFit (show HalfSourceBatchFit.eta<1 by
    norm_num [HalfSourceBatchFit.eta,HalfSourceBatchFit.b,bNumerator,bDenominator,R]) 4 512
  filter_upwards [h,eventually_ge_atTop (3:ℕ)] with n hn hn3
  have hs := (scale_bounds n hn3).2
  have hn' : (scale n:ℝ)≤n := by
    apply hs.trans
    simpa only [Real.rpow_one,mul_comm,mul_left_comm,mul_assoc] using hn
  exact_mod_cast hn'

lemma eventually_input_size_le_n (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ)≤(n:ℝ)^κ → U.size ≤ n := by
  have h := AsymptoticCosts.eventualPowerFit (show (0:ℝ)<1 by norm_num) 1
    (4*(Nat.ceil κ:ℝ)+1)
  filter_upwards [h,eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro U hU
  have hu := input_size_of_real_power n U κ (by omega) hU
  have hs := size_le_four_log n hn3
  have hl := PhaseGeometry.one_le_log_nat n hn3
  have huR : (U.size:ℝ)≤(Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := by exact_mod_cast hu
  have hmul := mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤(Nat.ceil κ:ℝ) by positivity)
  have hf : (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) ≤ n := by
    simpa only [Real.rpow_zero,Real.rpow_one,pow_one,mul_one] using hn
  have hbound : (U.size:ℝ)≤n := by
    calc
      (U.size:ℝ) ≤ (Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := huR
      _ ≤ (Nat.ceil κ:ℝ)*(4*Real.log (n:ℝ))+1 := by
        simpa only [add_comm] using add_le_add_right hmul 1
      _ ≤ (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) := by nlinarith
      _ ≤ n := hf
  exact_mod_cast hbound

lemma scale_add_one_upper (n : ℕ) (hn : 3≤n) :
    (scale n+1:ℝ) ≤ 513*(Real.log (n:ℝ))^4*(n:ℝ)^HalfSourceBatchFit.eta := by
  have hs := (scale_bounds n hn).2
  have hl := one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn) (n:=4)
  have he : 0≤HalfSourceBatchFit.eta := by
    norm_num [HalfSourceBatchFit.eta,HalfSourceBatchFit.b,bNumerator,bDenominator,R]
  have hx := Real.one_le_rpow (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)) he
  have hm := one_le_mul_of_one_le_of_one_le hl hx
  nlinarith

/-- A fixed coefficient absorbs the finite root degrees and validation depth;
no parameter-sized power is normalized to establish the time estimate. -/
def executionCoefficient : ℕ := 10000000000000000000000000000000000000000

theorem execute_finite_price (n U : ℕ) (hn : 4≤n) (hR : R≤n)
    (hP : scale n≤n) (hU : U.size≤n) :
    (execute n U).bitSteps ≤ executionCoefficient*(scale n+1)*n*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  have hbase : n.size+10+U.size ≤ B := by
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    omega
  have hf : ∀ z≤10*n,z.size≤B := by
    intro z hz
    have h1 := (Nat.size_le_size hz).trans (size_mul 10 n)
    have h10 : (10:ℕ).size=4 := by decide
    rw [h10] at h1
    omega
  have hr1 : rootWidth bNumerator bDenominator n ≤ B := by
    dsimp [rootWidth,B,registerWidth,bNumerator,bDenominator,R]
    omega
  have hr2 : rootWidth bNumerator (bDenominator*R) n ≤ B := by
    dsimp [rootWidth,B,registerWidth,bNumerator,bDenominator,R]
    omega
  have hpw : ∀ j≤4,(n.size^j).size≤B := by
    intro j hj
    have h := size_pow n.size j
    have hm := Nat.mul_le_mul hj (size_le_self n.size)
    dsimp [B,registerWidth,bNumerator,bDenominator,R]
    nlinarith
  have hprep := prepareWith_price bNumerator bDenominator R n U B (10*n)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa only [scale,roundedPower] using (show 8*scale n+8≤10*n by omega)) hf hr1 hr2 hpw
  have hprep' : (prepare n U).bitSteps ≤
    ((n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*R+10)+
      (8*scale n+2)*(2*(10*n)+12)+8*scale n+2*n.size+U.size+30)*(unit B+1) := by
    simpa only [prepare,HalfSourceBatchFit.scale,roundedPower] using hprep
  clear hprep
  have hencn := serialize_price B n (by omega)
  have hencU := serialize_price B U (by omega)
  change (BinaryMultiplierAdapter.encodeNat n).bitSteps ≤ unit B at hencn
  change (BinaryMultiplierAdapter.encodeNat U).bitSteps ≤ unit B at hencU
  have hval := validate_registers n U
  have hdec := decodePrepared_price n U
  have hcoef :
    (n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*R+10)+
      (8*scale n+2)*(2*(10*n)+12)+16*scale n+2*n.size+U.size+2*R+52 ≤
      executionCoefficient*(scale n+1)*n := by
    have hs := size_le_self n
    dsimp [bNumerator,bDenominator,R,executionCoefficient]
    nlinarith
  rw [execute_steps,prepareEncoded_steps,prepareEncoded_value]
  have htotal :
      (BinaryMultiplierAdapter.encodeNat n).bitSteps+(BinaryMultiplierAdapter.encodeNat U).bitSteps+
        (prepare n U).bitSteps+1+(validate (prepare n U).value).bitSteps+
        (decodeData (prepare n U).value).bitSteps+1 ≤
      ((n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*R+10)+
        (8*scale n+2)*(2*(10*n)+12)+16*scale n+2*n.size+U.size+2*R+52)*(unit B+1) := by
    nlinarith
  exact htotal.trans (Nat.mul_le_mul_right _ hcoef)

/-- Uniform setup bound for the actual selector, including input encoding,
trial division, all finite validation, and public metadata decoding. -/
theorem execute_bitSteps_eventually (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ)≤(n:ℝ)^κ → (execute n U).bitSteps≤(n:ℝ)^2 := by
  let C : ℝ := (executionCoefficient:ℝ)*513*unitCoefficient κ
  have hfit := AsymptoticCosts.eventualPowerFit (show (1+HalfSourceBatchFit.eta:ℝ)<2 by
    norm_num [HalfSourceBatchFit.eta,HalfSourceBatchFit.b,bNumerator,bDenominator,R]) 6 C
  filter_upwards [hfit,eventually_scale_le_n,eventually_input_size_le_n κ,
    eventually_ge_atTop (max 4 R)] with n hn hP hU hnlarge
  intro U hbound
  have hn4 : 4≤n := (le_max_left _ _).trans hnlarge
  have hnR : R≤n := (le_max_right _ _).trans hnlarge
  have hn3 : 3≤n := by omega
  have hfinite := execute_finite_price n U hn4 hnR hP (hU U hbound)
  have hfiniteR : ((execute n U).bitSteps:ℝ) ≤
      (executionCoefficient:ℝ)*(scale n+1:ℝ)*(n:ℝ)*(unit (registerWidth n U)+1:ℝ) := by exact_mod_cast hfinite
  have hs := scale_add_one_upper n hn3
  have hu := unit_le_log_square n U κ hn3 hbound
  have hc := unitCoefficient_pos κ
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  calc
    ((execute n U).bitSteps:ℝ) ≤
        (executionCoefficient:ℝ)*(scale n+1:ℝ)*(n:ℝ)*(unit (registerWidth n U)+1:ℝ) := hfiniteR
    _ ≤ (executionCoefficient:ℝ)*(513*(Real.log (n:ℝ))^4*(n:ℝ)^HalfSourceBatchFit.eta)*
        (n:ℝ)*(unitCoefficient κ*(Real.log (n:ℝ))^2) := by gcongr
    _ = C*(Real.log (n:ℝ))^6*(n:ℝ)^(1+HalfSourceBatchFit.eta) := by
      rw [Real.rpow_add hnpos,Real.rpow_one,show (6:ℕ)=4+2 by rfl,pow_add]
      dsimp [C]
      ring
    _ ≤ (n:ℝ)^2 := by simpa only [Real.rpow_two] using hn

/-- The actual adaptive APSP cap satisfies the same uniform selector bound. -/
theorem execute_apspCap_eventually (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W≤n^degree →
      (execute n (192*n*W+40)).bitSteps≤(n:ℝ)^2 := by
  filter_upwards [execute_bitSteps_eventually (degree+2:ℕ),eventually_ge_atTop (232:ℕ)] with n hn hn232
  intro W hW
  apply hn
  have hcap := ComputableParameters.apspCap_polynomial degree n W (by omega) hW
  have hpoly : 192*n*W+40 ≤ n^(degree+2) := by
    calc
      _ ≤ 232*n^(degree+1) := hcap
      _ ≤ n*n^(degree+1) := Nat.mul_le_mul_right _ hn232
      _ = n^(degree+2) := by rw [show degree+2=(degree+1)+1 by omega,pow_succ];ring
  exact_mod_cast hpoly


#print axioms prepare_correct
#print axioms validate_correct
#print axioms prepareEncoded_value
#print axioms configurationDecoded_eq
#print axioms execute_value
#print axioms execute_steps
#print axioms validate_registers
#print axioms decodePrepared_price
#print axioms registerWidth_le_log
#print axioms execute_finite_price
#print axioms execute_bitSteps_eventually
#print axioms execute_apspCap_eventually
end ThinMatrix.HalfSourceParameterExecution
