import BinaryAPSPHostCosts

/-! Prices for the actual stored-bit signed, optional and squaring host stages.
Oracle work is retained separately by the caller; these inequalities bound
only the caller's own binary operations, transfers and public controls. -/
namespace ThinMatrix.BinaryAPSPHostStages
open BinaryAPSPCaller BinaryAPSPHostCosts
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
local macro "bit_omega" : tactic => `(tactic| first | (unfold bits at *; omega) | omega)

theorem shift_fits {n : ℕ} (P : ℕ) (A : IntTable n) (u : Cell)
    (hA : Fits P A) (hu : bits u  ≤  P) : Fits (P+1) (shift A u).value := by
  intro i j
  simp only [shift,tabulate_get]
  have hc := hA i j
  exact (BinaryModularCell.add_size _ _).trans (by bit_omega)

theorem shift_price {n : ℕ} (P W : ℕ) (A : IntTable n) (u : Cell)
    (hA : Fits P A) (hu : bits u  ≤  P) (hW : P ≤ W) :
    (shift A u).bitSteps  ≤  n^2*tablePrice n W := by
  apply tabulate_price
  intro i j
  have hp := BinaryCell.add_price W (StoredMinPlusAPSP.decode A i j) u
    ((hA i j).trans hW) (hu.trans hW)
  exact hp.trans (by have h:=primitive_price_le W; bit_omega)

theorem signedProduct_fits {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (d : ℕ) (A B : IntTable n) (u v : Cell) :
    Fits (max (2*d+2) (max (bits u) (bits v))+2) (signedProduct O d A B u v).value := by
  intro i j
  have hc := bitScale_fits O d (shift A u).value (shift B v).value i j
  have hf := BinaryModularCell.sub_size
    (StoredMinPlusAPSP.decode (bitScale O d (shift A u).value (shift B v).value).value i j) u
  have hs := BinaryModularCell.sub_size
    (BinaryCell.sub (StoredMinPlusAPSP.decode
      (bitScale O d (shift A u).value (shift B v).value).value i j) u).value v
  simp only [signedProduct,tabulate_get]
  change bits (BinaryCell.sub (BinaryCell.sub _ u).value v).value  ≤  _
  change bits (BinaryCell.sub _ u).value  ≤  max _ _+1 at hf
  change bits (BinaryCell.sub _ v).value  ≤  max _ _+1 at hs
  bit_omega

theorem signedProduct_hostBits_le {n : ℕ} {Payload : Type} (hn : 0<n)
    (O : Oracle n Payload) (d P W : ℕ) (A B : IntTable n) (u v : Cell)
    (hA : Fits P A) (hB : Fits P B) (hu : bits u ≤ P) (hv : bits v ≤ P)
    (hW : P+2*d+12 ≤ W) :
    (signedProduct O d A B u v).hostBits ≤ (6*d+4)*n^2*tablePrice n W := by
  let core := bitScale O d (shift A u).value (shift B v).value
  have hcore := bitScale_hostBits_le hn O d (P+1) W _ _
    (shift_fits P A u hA hu) (shift_fits P B v hB hv) (by bit_omega)
  have hfits : Fits (2*d+2) core.value := bitScale_fits O d _ _
  have hshiftA := shift_price P W A u hA hu (by bit_omega)
  have hshiftB := shift_price P W B v hB hv (by bit_omega)
  have hresult :
      (tabulate (fun i j =>
        let first := BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u
        let second := BinaryCell.sub first.value v
        (⟨second.value,first.bitSteps+second.bitSteps⟩ : Result Cell))).bitSteps ≤
          n^2*tablePrice n W := by
    apply tabulate_price
    intro i j
    have hf := BinaryModularCell.sub_size (StoredMinPlusAPSP.decode core.value i j) u
    have hfw : bits (BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u).value ≤ W := by
      change bits (BinaryCell.sub _ _).value  ≤  max _ _+1 at hf
      have hc := hfits i j
      bit_omega
    have hp0 := BinaryCell.sub_price W (StoredMinPlusAPSP.decode core.value i j) u
      ((hfits i j).trans (by bit_omega)) (hu.trans (by bit_omega))
    have hp1 := BinaryCell.sub_price W (BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u).value v
      hfw (hv.trans (by bit_omega))
    have hp := primitive_price_le W
    change (BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u).bitSteps+
      (BinaryCell.sub (BinaryCell.sub (StoredMinPlusAPSP.decode core.value i j) u).value v).bitSteps ≤ _
    bit_omega
  change core.hostBits+(shift A u).bitSteps+(shift B v).bitSteps+_ ≤ _
  change core.hostBits ≤ _ at hcore
  nlinarith only [hcore,hshiftA,hshiftB,hresult]

theorem encodeOptional_fits {n : ℕ} (P : ℕ) (s : Cell) (A : OptionalTable n)
    (hs : bits s ≤ P) (hA : OptionalFits P A) :
    Fits P (tabulate (fun i j => encodeOptionalCell s (StoredMinPlusAPSP.decode A i j))).value := by
  intro i j
  simp only [tabulate_get]
  cases h : StoredMinPlusAPSP.decode A i j with
  | none => simpa only [encodeOptionalCell,bits,BinaryCell.copy_view] using hs
  | some c => simpa only [encodeOptionalCell,bits,BinaryCell.copy_view] using hA i j c h

theorem encodeOptional_price {n : ℕ} (P W : ℕ) (s : Cell) (A : OptionalTable n)
    (hs : bits s ≤ P) (hA : OptionalFits P A) (hW : P ≤ W) :
    (tabulate (fun i j => encodeOptionalCell s (StoredMinPlusAPSP.decode A i j))).bitSteps ≤
      n^2*tablePrice n W := by
  apply tabulate_price
  intro i j
  have hp := primitive_price_le W
  cases h : StoredMinPlusAPSP.decode A i j with
  | none =>
    have hc := BinaryCell.copy_price W s (hs.trans hW)
    change (BinaryCell.copy s).bitSteps ≤ _
    bit_omega
  | some c =>
    have hc := BinaryCell.copy_price W c ((hA i j c h).trans hW)
    change (BinaryCell.copy c).bitSteps ≤ _
    bit_omega

theorem restoreCell_fits (P : ℕ) (threshold c : Cell) (hc : bits c ≤ P)
    (out : Cell) (hout : (restoreCell threshold c).value=some out) : bits out ≤ P := by
  by_cases h : (less threshold c).value=true
  · simp only [restoreCell,h,if_true] at hout
    contradiction
  · simp only [restoreCell,h] at hout
    have he := Option.some.inj hout
    rw [←he]
    simpa only [bits,BinaryCell.copy_view] using hc

theorem restoreCell_price (P W : ℕ) (threshold c : Cell)
    (ht : bits threshold ≤ P) (hc : bits c ≤ P) (hW : P ≤ W) :
    (restoreCell threshold c).bitSteps ≤ scalarPrice W := by
  have hp := BinaryModularCell.signedLess_price W threshold c (ht.trans hW) (hc.trans hW)
  have hcopy := BinaryCell.copy_price W c (hc.trans hW)
  have hbase : (W+1)^2 ≤ (W+3)^3 :=
    (Nat.pow_le_pow_left (by bit_omega) 2).trans
      (Nat.pow_le_pow_right (by bit_omega) (by decide))
  have hpow : (W+1)^3 ≤ (W+3)^3 := Nat.pow_le_pow_left (by bit_omega) 3
  change (less threshold c).bitSteps ≤ 100000*(W+1)^3 at hp
  by_cases h : (less threshold c).value=true
  · simp only [restoreCell,h,if_true]
    simp only [scalarPrice,BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit] at *
    nlinarith only [hp,hcopy,hbase,hpow]
  · simp only [restoreCell,h,Bool.false_eq_true,if_false]
    simp only [scalarPrice,BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit] at *
    nlinarith only [hp,hcopy,hbase,hpow]

theorem sentinel_control_sizes (B : ℕ) :
    B.size ≤ (APSPAlgorithm.sentinel B).size ∧
      (2*(B : ℤ)).natAbs.size ≤ (APSPAlgorithm.sentinel B).size := by
  constructor
  · apply Nat.size_le_size
    unfold APSPAlgorithm.sentinel
    bit_omega
  · rw [Int.natAbs_mul,show (2 : ℤ).natAbs=2 from rfl,Int.natAbs_natCast]
    apply Nat.size_le_size
    unfold APSPAlgorithm.sentinel
    bit_omega

theorem optionalProduct_fits {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (B P : ℕ) (A C : OptionalTable n)
    (hP : 2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+
      (APSPAlgorithm.sentinel B).size+6 ≤ P) :
    OptionalFits P (optionalProduct O B A C).value := by
  let s := BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)
  let encodedA := (tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode A i j))).value
  let encodedC := (tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode C i j))).value
  let core := signedProduct O (MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B))
    encodedA encodedC s.value s.value
  have hs : bits s.value=(APSPAlgorithm.sentinel B).size := by
    simp only [s,bits,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view,Int.natAbs_natCast]
  have hfits := signedProduct_fits O (MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B))
    encodedA encodedC s.value s.value
  intro i j out hout
  apply restoreCell_fits P _ (StoredMinPlusAPSP.decode core.value i j) ?_ out
    (by simpa only [optionalProduct,tabulate_get] using hout)
  have hc : bits (StoredMinPlusAPSP.decode core.value i j) ≤
      max (2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+2)
        (max (bits s.value) (bits s.value))+2 := hfits i j
  rw [hs,max_self] at hc
  bit_omega

theorem optionalProduct_hostBits_le {n : ℕ} {Payload : Type} (hn : 0<n)
    (O : Oracle n Payload) (B P W : ℕ) (A C : OptionalTable n)
    (hA : OptionalFits P A) (hC : OptionalFits P C)
    (hP : 2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+
      (APSPAlgorithm.sentinel B).size+6 ≤ P)
    (hW : P+2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+12 ≤ W) :
    (optionalProduct O B A C).hostBits ≤
      (6*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+10)*n^2*tablePrice n W := by
  let d := MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)
  let s := BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)
  let threshold := BinaryMultiplierAdapter.encodeInteger (2*(B : ℤ))
  let encodedA := tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode A i j))
  let encodedC := tabulate (fun i j => encodeOptionalCell s.value (StoredMinPlusAPSP.decode C i j))
  let core := signedProduct O d encodedA.value encodedC.value s.value s.value
  have hs : bits s.value=(APSPAlgorithm.sentinel B).size := by
    simp only [s,bits,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view,Int.natAbs_natCast]
  have ht : bits threshold.value ≤ (APSPAlgorithm.sentinel B).size := by
    simpa only [threshold,bits,BinaryCell.view,BinaryMultiplierAdapter.encodeInteger_view] using
      (sentinel_control_sizes B).2
  have hsp : bits s.value ≤ P := by rw [hs]; bit_omega
  have hcore := signedProduct_hostBits_le hn O d P W encodedA.value encodedC.value s.value s.value
    (encodeOptional_fits P s.value A hsp hA) (encodeOptional_fits P s.value C hsp hC) hsp hsp hW
  have heA := encodeOptional_price P W s.value A hsp hA (by bit_omega)
  have heC := encodeOptional_price P W s.value C hsp hC (by bit_omega)
  have hfits : Fits P core.value := by
    intro i j
    have hf : bits (StoredMinPlusAPSP.decode core.value i j) ≤
        max (2*d+2) (max (bits s.value) (bits s.value))+2 :=
      signedProduct_fits O d encodedA.value encodedC.value s.value s.value i j
    rw [hs,max_self] at hf
    change _ ≤ P
    bit_omega
  have hrestore : (tabulate (fun i j => restoreCell threshold.value
      (StoredMinPlusAPSP.decode core.value i j))).bitSteps ≤ n^2*tablePrice n W := by
    apply tabulate_price
    intro i j
    exact restoreCell_price P W threshold.value _ (ht.trans (by bit_omega)) (hfits i j) (by bit_omega)
  have hsetup : s.bitSteps+threshold.bitSteps+8*(B.size+2)^2 ≤ n^2*tablePrice n W := by
    have hsprice := BinaryMultiplierAdapter.encodeInteger_cost (APSPAlgorithm.sentinel B : ℤ)
    have htprice := BinaryMultiplierAdapter.encodeInteger_cost (2*(B : ℤ))
    have hB := (sentinel_control_sizes B).1
    have htwo := (sentinel_control_sizes B).2
    simp only [Int.natAbs_natCast] at hsprice
    have hsW : (APSPAlgorithm.sentinel B).size ≤ W := by bit_omega
    have hp : (W+2)^2 ≤ (W+3)^3 :=
      (Nat.pow_le_pow_left (by bit_omega) 2).trans
        (Nat.pow_le_pow_right (by bit_omega) (by decide))
    have he : s.bitSteps+threshold.bitSteps+8*(B.size+2)^2 ≤ scalarPrice W := by
      change (BinaryMultiplierAdapter.encodeInteger (APSPAlgorithm.sentinel B : ℤ)).bitSteps+
        (BinaryMultiplierAdapter.encodeInteger (2*(B : ℤ))).bitSteps+8*(B.size+2)^2 ≤ _
      have hp0 := Nat.pow_le_pow_left (by bit_omega : (APSPAlgorithm.sentinel B).size+1 ≤ W+2) 2
      have hp1 := Nat.pow_le_pow_left (by bit_omega : (2*(B : ℤ)).natAbs.size+1 ≤ W+2) 2
      have hp2 := Nat.pow_le_pow_left (by bit_omega : B.size+2 ≤ W+2) 2
      unfold scalarPrice
      nlinarith only [hsprice,htprice,hp0,hp1,hp2,hp]
    have hn2 : scalarPrice W ≤ n^2*tablePrice n W := by
      apply (show scalarPrice W ≤ tablePrice n W by unfold tablePrice; bit_omega).trans
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact he.trans hn2
  change core.hostBits+s.bitSteps+threshold.bitSteps+encodedA.bitSteps+encodedC.bitSteps+
    (tabulate (fun i j => restoreCell threshold.value (StoredMinPlusAPSP.decode core.value i j))).bitSteps+
    8*(B.size+2)^2 ≤ _
  change core.hostBits ≤ _ at hcore
  change encodedA.bitSteps ≤ _ at heA
  change encodedC.bitSteps ≤ _ at heC
  nlinarith only [hcore,heA,heC,hrestore,hsetup]

theorem initialCell_fits (P : ℕ) (diagonal : Bool) (a : Option Cell)
    (ha : ∀c,a=some c→bits c ≤ P) (out : Cell)
    (hout : (initialCell diagonal a).value=some out) : bits out ≤ P := by
  cases diagonal with
  | false =>
    cases a with
    | none => simp [initialCell] at hout
    | some c =>
      have hc := ha c rfl
      simp only [initialCell,Bool.false_eq_true,if_false] at hout
      have he := Option.some.inj hout
      rw [←he]
      simpa only [bits,BinaryCell.copy_view] using hc
  | true =>
    cases a with
    | none =>
      have he : BinaryCell.zero=out := Option.some.inj hout
      rw [←he]
      simp
    | some c =>
      have hc := ha c rfl
      simp only [initialCell,if_true] at hout
      split at hout
      · have he := Option.some.inj hout
        rw [←he]
        simpa only [bits,BinaryCell.copy_view] using hc
      · have he := Option.some.inj hout
        rw [←he]
        simp

theorem initialCell_price (P W : ℕ) (diagonal : Bool) (a : Option Cell)
    (ha : ∀c,a=some c→bits c ≤ P) (hW : P ≤ W) :
    (initialCell diagonal a).bitSteps ≤ scalarPrice W := by
  cases a with
  | none => cases diagonal <;> simp [initialCell,scalarPrice]
  | some c =>
    have hc := (ha c rfl).trans hW
    have hp := BinaryModularCell.signedLess_price W c BinaryCell.zero hc (by simp)
    have hcopy := BinaryCell.copy_price W c hc
    change (less c BinaryCell.zero).bitSteps ≤ 100000*(W+1)^3 at hp
    have hbase : (W+1)^2 ≤ (W+3)^3 :=
      (Nat.pow_le_pow_left (by bit_omega) 2).trans
        (Nat.pow_le_pow_right (by bit_omega) (by decide))
    have hpow : (W+1)^3 ≤ (W+3)^3 := Nat.pow_le_pow_left (by bit_omega) 3
    cases diagonal <;> simp only [initialCell,Bool.false_eq_true,if_false,if_true]
    · unfold scalarPrice BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit at *
      nlinarith only [hp,hcopy,hbase,hpow]
    · split <;>
        simp only [scalarPrice,BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit] at * <;>
        nlinarith only [hp,hcopy,hbase,hpow]

theorem initial_fits {n : ℕ} (P : ℕ) (w : OptionalTable n) (hw : OptionalFits P w) :
    OptionalFits P (tabulate (fun i j => initialCell (decide (i=j)) (StoredMinPlusAPSP.decode w i j))).value := by
  intro i j out hout
  exact initialCell_fits P _ _ (hw i j) out (by simpa only [tabulate_get] using hout)

theorem squared_fits {n : ℕ} {Payload : Type} (O : Oracle n Payload)
    (w : OptionalTable n) (B P k : ℕ) (hw : OptionalFits P w)
    (hP : 2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+
      (APSPAlgorithm.sentinel B).size+6 ≤ P) :
    OptionalFits P (squared O w B k).value := by
  cases k with
  | zero => exact initial_fits P w hw
  | succ k => exact optionalProduct_fits O B P _ _ hP

theorem squared_hostBits_le {n : ℕ} {Payload : Type} (hn : 0<n)
    (O : Oracle n Payload) (w : OptionalTable n) (B P W k : ℕ)
    (hw : OptionalFits P w)
    (hP : 2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+
      (APSPAlgorithm.sentinel B).size+6 ≤ P)
    (hW : P+2*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+k+20 ≤ W) :
    (squared O w B k).hostBits ≤
      (1+k*(6*MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)+11))*n^2*tablePrice n W := by
  let d := MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B)
  induction k generalizing W with
  | zero =>
    have ht : (tabulate (fun i j => initialCell (decide (i=j))
        (StoredMinPlusAPSP.decode w i j))).bitSteps ≤ n^2*tablePrice n W := by
      apply tabulate_price
      intro i j
      exact initialCell_price P W _ _ (hw i j) (by bit_omega)
    simpa only [squared,Nat.zero_mul,Nat.add_zero,Nat.one_mul] using ht
  | succ k ih =>
    let previous := squared O w B k
    have hprevious := ih W (by bit_omega)
    have hfits : OptionalFits P previous.value := squared_fits O w B P k hw hP
    have hcurrent := optionalProduct_hostBits_le hn O B P W previous.value previous.value
      hfits hfits hP (by bit_omega)
    have hcontrol : previous.calls.length+4 ≤ n^2*tablePrice n W := by
      have hlen : previous.calls.length=k*(2*d) := squared_calls O w B k
      have hk : k ≤ W := by bit_omega
      have hd : d ≤ W := by change MinPlusReduction.signedLevels (APSPAlgorithm.sentinel B) ≤ W; bit_omega
      have hmul := Nat.mul_le_mul hk (Nat.mul_le_mul_left 2 hd)
      have hp : W^2 ≤ (W+3)^3 :=
        (Nat.pow_le_pow_left (by bit_omega) 2).trans
          (Nat.pow_le_pow_right (by bit_omega) (by decide))
      have he : previous.calls.length+4 ≤ scalarPrice W := by
        rw [hlen]
        unfold scalarPrice
        nlinarith only [hmul,hp]
      exact he.trans ((show scalarPrice W ≤ tablePrice n W by unfold tablePrice; bit_omega).trans
        (Nat.le_mul_of_pos_left _ (by positivity)))
    change previous.hostBits+(optionalProduct O B previous.value previous.value).hostBits+
      previous.calls.length+4 ≤ _
    change previous.hostBits ≤ _ at hprevious
    nlinarith only [hprevious,hcurrent,hcontrol]

#print axioms shift_fits
#print axioms signedProduct_fits
#print axioms signedProduct_hostBits_le
#print axioms optionalProduct_fits
#print axioms optionalProduct_hostBits_le
#print axioms initial_fits
#print axioms squared_fits
#print axioms squared_hostBits_le

end ThinMatrix.BinaryAPSPHostStages
