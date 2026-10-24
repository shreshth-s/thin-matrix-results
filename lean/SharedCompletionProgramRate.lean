import SharedCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ThinMatrix.SharedCompletionProgramRate
open scoped BigOperators
open BinaryCell SharedFullyPrefixWork SharedCompletionRate

/-- One fixed, proved CW program supplies the required rate for every source
support, original-ID request list, and complete coefficient bank. All native
indexed controls, binary arithmetic, selectors and one-time size setup are
included. The lower independent-fit hypothesis is explicit. -/
theorem exists_schedule_rate : ∃ scheme : RectangularBatch.Scheme, scheme.Valid ∧
    scheme.num=861 ∧ scheme.den=500 ∧ scheme.z=15 ∧
    ∃ K : ℝ, 0 < K ∧ ∀ P ell r B C A Z : ℕ,
      ∀ hD : 0 < CappedSubsetList.count ell r, ∀ hA : 0 < A, ∀ hZ : 0 < Z,
      ∀ hf : (A-1)^scheme.den ≤ (CappedSubsetList.count ell r)^scheme.num,
      ∀ hl : Z ≤ (CappedSubsetList.count ell r)^scheme.z,
      ∀ xs : Vector (CappedPrefixProgram.Prepared P ell r C) B,
      ∀ H W price L : ℕ, ∀ _hH : 1 ≤ H,
      (∀ b pair,PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H) →
      ∀ requests : Array (Vector (Fin 4) (P+ell)),
      Z ≤ B*C → Z=(CappedSubsetList.count ell r)^15 →
      ((CappedSubsetList.count ell r:ℝ)^a ≤ (A:ℝ)) →
      ((A:ℝ) ≤ 2*(CappedSubsetList.count ell r:ℝ)^a) →
      CappedSubsetList.count ell r ≤ A → CappedSubsetList.count ell r ≤ B*C → B ≤ B*C →
      1 ≤ L → P+ell+1 ≤ L → W+1 ≤ L →
      (CappedSubsetList.count ell r).size+3 ≤ L →
      scheme.q.size+(CappedSubsetList.count ell r).size+6 ≤ L →
      (CappedSubsetList.count ell r).size+H.size+6 ≤ L →
      (∀ pair i,SharedFullyAddressedBatch.AddressFits
        (RoutedPrefixBatch.ids (RoutedPrefixBatch.prepare xs requests).value pair (PrefixBatchSchedule.digits i)).value.length
        (CappedSubsetList.count ell r) (B*C) A Z W) →
      ((SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).bitSteps+
        price*(SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value).control:ℝ) ≤
      K*(price+1)*(L:ℝ)^5*((requests.size:ℝ)*(B*C)*(CappedSubsetList.count ell r:ℝ)^beta+
        ((2^ell*4^P:ℕ):ℝ)*(B*C)*(CappedSubsetList.count ell r:ℝ)^gamma) := by
  obtain ⟨scheme,hvalid,hnum,hden,hz,K,hK,hcost⟩ := SharedAddressedCWCosts.exists_uniform_work_budget
  refine ⟨scheme,hvalid,hnum,hden,hz,100000+2*K,by positivity,?_⟩
  intro P ell r B C A Z hD hA hZ hf hl xs H W price L hH hx requests hfit hZeq hAlo hAhi hDA hDQ hB hL hlen hWlog hdlog hqlog hHlog hW
  let D := CappedSubsetList.count ell r
  let G := 2^ell*4^P
  let Q := B*C
  let M := requests.size
  let shape := SharedMatrixSetup.prepare scheme hD hf hl
  let E := shape.bitSteps+scheduleControl P ell+M*requestUnit D Q ell W+G*groupUnit D B Q A P ell W
  let V := SharedAddressedCWCosts.workCost scheme shape.value.depth H
  let out := SharedFullyPrefixSchedule.execute scheme hD hA hZ hf hl requests (RoutedPrefixBatch.prepare xs requests).value
  let T := out.bitSteps+price*out.control
  have hQ : 1 ≤ Q := (show 1 ≤ Z by omega).trans hfit
  have hE : E ≤ 50000*L^3*Q*(M+G*A) :=
    SharedCompletionExtras.all_extras scheme hD hf hl M B Q P ell W L hQ (by omega) hDQ hDA hB hL hlen hWlog hdlog hqlog
  have hV : (V:ℝ) ≤ K*(L:ℝ)^5*(D:ℝ)^CWFiniteBase.exponent := by
    apply (hcost D A Z hD hf hl H).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact_mod_cast Nat.pow_le_pow_left hHlog 5
  have hT : T*A*Z ≤ (price+1)*(E*A*Z+2*(M+G*A)*Q*V) :=
    SharedFullyPrefixPrices.schedule_price_volume scheme hD hA hZ hf hl xs H W price hH hx requests hfit hW
  have hZR : (Z:ℝ)=(D:ℝ)^(15:ℝ) := by
    rw [hZeq]
    norm_cast
  have hscaled : (T:ℝ)*(A:ℝ)*(Z:ℝ) ≤ ((price:ℝ)+1)*((E:ℝ)*(A:ℝ)*(Z:ℝ)+
      2*((M:ℝ)+(G:ℝ)*(A:ℝ))*(Q:ℝ)*(V:ℝ)) := by exact_mod_cast hT
  have hER : (E:ℝ) ≤ 50000*(L:ℝ)^3*(Q:ℝ)*((M:ℝ)+(G:ℝ)*(A:ℝ)) := by exact_mod_cast hE
  have hr := volume_to_rate (D:ℝ) M G Q A Z L K price T E V
    (by exact_mod_cast hD) (by positivity) (by positivity) (by positivity)
    hAlo hAhi hZR (by exact_mod_cast hL) hK.le (by positivity) hER hV hscaled
  simpa only [T,M,G,Q,out,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hr

#print axioms exists_schedule_rate
end ThinMatrix.SharedCompletionProgramRate
