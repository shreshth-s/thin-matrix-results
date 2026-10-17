import BinaryBackendExecution
import BinaryHighCost
import GlobalAddressBitBounds
import BackendCostRefinement
import AlignedAPSPCosts
import ComputedReductionCosts

/-!
# Closed resource collection for the binary stored backend

The bounds refer to the counters returned with the actual stored binary
arrays. Source, LOW and HIGH caps are propagated from the original input
cells. Full cyclic vectors, both band families, and every pair of bands
remain explicit. Public finite-index and array actions use the same model
as the component programs; machine-address compilation is separate.
-/
namespace ThinMatrix.BinarySourceFactor
open ThinMatrixBackend BackendCostRefinement BinaryBandSource SourceFormation

/-- Uniform binary price for original 0/1 source materialization. -/
def sourceFactor (L m : ℕ) : ℕ :=
  10000+10000*BinarySourceFormation.bitUnit L (L-m) 2

theorem add_const_scale {B C F a : ℕ} (h : B ≤ F*C) (hF : 1 ≤ F) :
    B+a ≤ F*(C+a) := by
  have ha : a ≤ F*a := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

theorem tableBudget_scale (n B C F : ℕ) (h : B ≤ F*C) (hF : 1 ≤ F) :
    binaryTableBudget n B ≤ F*binaryTableBudget n C := by
  have hh := Nat.mul_le_mul_right (2^n) (add_const_scale (a:=16*n) h hF)
  simpa only [binaryTableBudget,Nat.mul_assoc] using hh

theorem nestedBudget_scale (dims : List ℕ) (B C F : ℕ) (h : B ≤ F*C) (hF : 1 ≤ F) :
    SourceCosts.nestedBudget dims B ≤ F*SourceCosts.nestedBudget dims C := by
  induction dims with
  | nil => exact h
  | cons n ds ih => exact tableBudget_scale n _ _ F ih hF

theorem rawReadBudget_one (L m : ℕ) :
    rawReadBudget L m 1 ≤ 1000*inputEntryAllowance L m := by
  let P := L+m+1
  let X := (2:ℕ)^L
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by decide)
  have hLP : (L+1)^2 ≤ P^3 := by
    calc
      _  ≤  P^2 := Nat.pow_le_pow_left (by dsimp [P]; omega) 2
      _  ≤  P^3 := Nat.pow_le_pow_right hP (by decide)
  have hP3 : 1 ≤ P^3 := Nat.one_le_pow _ _ hP
  have hpX : 1 ≤ P^3*X := by nlinarith
  have hterm : (L+1)^2*(X+1) ≤ 2*(P^3*X) := by
    calc
      _  ≤  P^3*(2*X) := Nat.mul_le_mul hLP (by omega)
      _ = _ := by ring
  have hsmall : (L+1)^2 ≤ P^3*X := hLP.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hcube : P^3 ≤ P^3*X := Nat.le_mul_of_pos_right _ (by omega)
  unfold rawReadBudget inputEntryAllowance BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  change 64*(L+1)^2*(X+1)+8*(100*(1+1)^2)+16*(L+1)^2+100*P^3 ≤ 1000*(100*P^3*X)
  nlinarith

theorem adapterBudget_one (L m q : ℕ) :
    BinaryInputAdapter.adapterBudget L m q (rawReadBudget L m 1) ≤ 1000*inputBudget L m q := by
  have hr := rawReadBudget_one L m
  have hb := Nat.mul_le_mul_right q (add_const_scale (a:=8) hr (by decide))
  have hb' : (rawReadBudget L m 1+8)*q ≤ 1000*((inputEntryAllowance L m+8)*q) := by
    simpa only [Nat.mul_assoc] using hb
  exact nestedBudget_scale [L,L,L-m,m,m] _ _ 1000 hb' (by decide)

theorem cachedReadBudget_one (L m : ℕ) :
    cachedReadBudget L m 1 ≤ 401*SourceCosts.readerBudget L m := by
  unfold cachedReadBudget SourceCosts.readerBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  nlinarith

theorem sourceBudget_scale (L m k q B C F : ℕ) (h : B ≤ F*C) (hF : 1 ≤ F) :
    sourceBudget L m k q B ≤ F*sourceBudget L m k q C := by
  have hc := add_const_scale (a:=8*(k+1)+19) h hF
  have hw := Nat.mul_le_mul_right (2^k*q) hc
  have hm : metadataCost L m k ≤ F*metadataCost L m k := Nat.le_mul_of_pos_left _ (by omega)
  have hbase : wordBudget L m k q B ≤ F*wordBudget L m k q C := by
    unfold wordBudget wordCoefficientBudget
    nlinarith
  have hf := Nat.mul_le_mul_right (12^L) (add_const_scale (a:=56*L) hbase hF)
  simpa only [sourceBudget,Nat.mul_assoc] using hf

theorem preparationBudget_one (L m q : ℕ) (_hm : m ≤ L) (hq : 1 ≤ q) :
    preparationBudget L m q 1 ≤ sourceFactor L m*bandSourceBudget L m q := by
  have hi := adapterBudget_one L m q
  have hs := sourceBudget_scale L m (L-m) q _ _ 401 (cachedReadBudget_one L m) (by decide)
  have hpos : 1 ≤ sourceBudget L m (L-m) q (SourceCosts.readerBudget L m) := by
    have hp : 0 < sourceBudget L m (L-m) q (SourceCosts.readerBudget L m) := by
      unfold sourceBudget wordBudget metadataCost
      positivity
    omega
  have hs8 : sourceBudget L m (L-m) q (cachedReadBudget L m 1)+8 ≤
      409*sourceBudget L m (L-m) q (SourceCosts.readerBudget L m) := by omega
  let U := BinarySourceFormation.bitUnit L (L-m) 2
  let S := sourceBudget L m (L-m) q (SourceCosts.readerBudget L m)
  let I := inputBudget L m q
  let F := sourceFactor L m
  have hs8' := Nat.mul_le_mul_right ((2*m+1)*U) hs8
  have htail : (sourceBudget L m (L-m) q (cachedReadBudget L m 1)+8)*(2*m+1)*U ≤
      (409*U)*((2*m+1)*S) := by
    convert hs8' using 1 <;> ring
  have hF : 409*U ≤ F := by dsimp [F,sourceFactor,U]; omega
  have hF' : 1000 ≤ F*4 := by dsimp [F,sourceFactor]; omega
  have hi' : 1000*I ≤ F*(4*I) := by
    convert Nat.mul_le_mul_right I hF' using 1
    ring
  have ht' : (409*U)*((2*m+1)*S) ≤ F*((2*m+1)*S) :=
    Nat.mul_le_mul_right _ hF
  change BinaryInputAdapter.adapterBudget L m q (rawReadBudget L m 1)+
    (sourceBudget L m (L-m) q (cachedReadBudget L m 1)+8)*(2*m+1)*U ≤
      F*(4*I+(2*m+1)*S)
  calc
    _ ≤ 1000*I+(409*U)*((2*m+1)*S) := Nat.add_le_add hi htail
    _ ≤ F*(4*I)+F*((2*m+1)*S) := Nat.add_le_add hi' ht'
    _ = _ := by ring

/-- The source conversion factor is polynomial in the logarithmic ambient
input size whenever the physical length is logarithmic. -/
theorem sourceFactor_polynomial (n L m cL : ℕ) (hL : L ≤ cL*(n.size+1)) :
    sourceFactor L m ≤ 20000000*(2*cL+3)^3*(n.size+1)^3 := by
  have hW : L+(L-m)+2+1 ≤ (2*cL+3)*(n.size+1) := by
    have hm := Nat.sub_le L m
    nlinarith
  have hcube := Nat.pow_le_pow_left hW 3
  have hS : 1 ≤ (2*cL+3)^3*(n.size+1)^3 := by
    have hpos : 0 < (2*cL+3)^3*(n.size+1)^3 := by positivity
    omega
  unfold sourceFactor BinarySourceFormation.bitUnit BinarySourceFormation.formationWidth
  change 10000+10000*(1000*(L+(L-m)+2+1)^3) ≤ _
  have he : ((2*cL+3)*(n.size+1))^3 = (2*cL+3)^3*(n.size+1)^3 := mul_pow ..
  rw [he] at hcube
  nlinarith

#print axioms sourceFactor_polynomial
#print axioms rawReadBudget_one
#print axioms adapterBudget_one
#print axioms preparationBudget_one
end ThinMatrix.BinarySourceFactor

namespace ThinMatrix.BinaryHighPolylog
open BinaryHighCost
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem rawStoredFactor_power_bound (L m : ℕ) :
    rawStoredFactor L (2^(L+m))≤10000000*(2*L+2)^3*(7*L+m+12)^2 := by
  have he : rawStoredFactor L (2^(L+m))=
      8000000*(2*L+1)^2*(7*L+m+12)^2*(2*L+2)+
        800*(7*L+m+12)^2+800*(L+m+2)^2+6*L+8 := by
    simp only [rawStoredFactor,storedFactor,encoderFactor,runFactor,commonWidth,
      BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit,Nat.size_pow]
    ring
  let E:=(2*L+2)^3*(7*L+m+12)^2
  have hE : (7*L+m+12)^2≤E :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hsmall : (L+m+2)^2≤E :=
    (Nat.pow_le_pow_left (by omega) 2).trans hE
  have hlin : 6*L+8≤E := by
    have hs : 7*L+m+12≤(7*L+m+12)^2 := le_self_pow₀ (by omega) (by decide : (2:ℕ)≠0)
    exact (show 6*L+8≤7*L+m+12 by omega).trans (hs.trans hE)
  have hlead : 8000000*(2*L+1)^2*(7*L+m+12)^2*(2*L+2)≤8000000*E := by
    calc
      _≤8000000*(2*L+2)^2*(7*L+m+12)^2*(2*L+2) := by gcongr;omega
      _=8000000*E := by dsimp [E];ring
  have hrhs : 10000000*(2*L+2)^3*(7*L+m+12)^2=10000000*E := by dsimp [E];ring
  rw [he,hrhs]
  omega

/-- Explicit polynomial factor for the actual HIGH source encoder. -/
theorem rawStoredFactor_polylog (L m n cL cm : ℕ)
    (hL : L≤cL*n.size) (hm : m≤cm*n.size) :
    rawStoredFactor L (2^(L+m))≤
      (10000000*(2*cL+2)^3*(7*cL+cm+12)^2)*(n.size+1)^5 := by
  have hL' : 2*L+2≤(2*cL+2)*(n.size+1) := by nlinarith
  have hW : 7*L+m+12≤(7*cL+cm+12)*(n.size+1) := by nlinarith
  calc
    _≤10000000*(2*L+2)^3*(7*L+m+12)^2 := rawStoredFactor_power_bound L m
    _≤10000000*((2*cL+2)*(n.size+1))^3*((7*cL+cm+12)*(n.size+1))^2 := by gcongr
    _=_ := by ring

#print axioms rawStoredFactor_power_bound
#print axioms rawStoredFactor_polylog
end ThinMatrix.BinaryHighPolylog


namespace ThinMatrix.BinaryHighBudget
open scoped BigOperators
open BinaryHighTable HighBoxDP

abbrev S (L q : ℕ) := L+q.log2+1
abbrev A (L m : ℕ) := AdaptiveBitBounds.highInputBudget L m 1
abbrev V (q A : ℕ) := q+BinaryMultiplierAdapter.workBound q A

theorem S_pos (L q : ℕ) : 1 ≤ S L q := by dsimp [S]; omega

theorem fftWork_le_adapter (q A : ℕ) : fftWorkBound q A ≤ BinaryMultiplierAdapter.workBound q A := by
  have hq := BinaryMultiplierAdapter.log2_le_size q
  have hA := BinaryMultiplierAdapter.log2_le_size A
  have h1 : q.log2+3 ≤ BinaryMultiplierAdapter.width q A := by unfold BinaryMultiplierAdapter.width; omega
  have h2 : q.log2+A.log2+102 ≤ BinaryMultiplierAdapter.width q A := by unfold BinaryMultiplierAdapter.width; omega
  unfold fftWorkBound
  calc
    _ ≤ 295147905179352825856*(BinaryMultiplierAdapter.width q A)*q*
      (BinaryMultiplierAdapter.width q A)^10 := by gcongr
    _ = 295147905179352825856*q*(BinaryMultiplierAdapter.width q A)^11 := by ring
    _ ≤ _ := by unfold BinaryMultiplierAdapter.workBound; gcongr; norm_num

theorem highLayerFactor_bound (L q : ℕ) [NeZero q] :
    ArrayKeys.highLayerFactor L q 0 ≤ 1000*(S L q)^3*q := by
  have hq : 1≤q := NeZero.pos q
  have hP : 1≤(L+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h1 : 300*(L+1)^3 ≤ 300*(L+1)^3*q := Nat.le_mul_of_pos_right _ hq
  have h2 : 11*q ≤ 11*((L+1)^3*q) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left q hP)
  calc
    _ = 96*L^3+96*L^2+58*L+13+11*q := by unfold ArrayKeys.highLayerFactor; ring
    _ ≤ 300*(L+1)^3+11*q := by nlinarith
    _ ≤ 1000*(L+1)^3*q := by nlinarith
    _ ≤ _ := by gcongr; dsimp [S]; omega

theorem baseBudget_bound (L q A : ℕ) [NeZero q] :
    baseBudget L q A ≤ 100*(S L q)^2*V q A := by
  have hq : 1≤q := NeZero.pos q
  have hP : 1≤(L+1)^2 := Nat.one_le_pow _ _ (by omega)
  have h1 : 24*(L+1)^2 ≤ 24*(L+1)^2*q := Nat.le_mul_of_pos_right _ hq
  have h2 : 3*q ≤ 3*((L+1)^2*q) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left q hP)
  have hm : 2*(6*L+q+1)+q+StoredHighDP.guardTests L ≤ 100*(S L q)^2*q := by
    calc
      _ = 4*L^2+18*L+3*q+2 := by unfold StoredHighDP.guardTests; ring
      _ ≤ 24*(L+1)^2+3*q := by nlinarith
      _ ≤ 100*(L+1)^2*q := by nlinarith
      _ ≤ _ := by gcongr; dsimp [S]; omega
  have h100 : 1≤100*(S L q)^2 := by have := S_pos L q; nlinarith
  have hf := fftWork_le_adapter q A
  have hf' : fftWorkBound q A ≤ 100*(S L q)^2*BinaryMultiplierAdapter.workBound q A :=
    hf.trans (Nat.le_mul_of_pos_left _ h100)
  unfold baseBudget V
  nlinarith



theorem highEntry_size_bound (L m q : ℕ) [NeZero q] (hm : m ≤ L) :
    (5^(2*L+1)*(q*(A L m)^2)).size ≤ 25*S L q := by
  have h5 : 5^(2*L+1) ≤ 2^(3*(2*L+1)) := by
    calc
      _ ≤ (2^3)^(2*L+1) := Nat.pow_le_pow_left (by norm_num) _
      _ = _ := by rw [← Nat.pow_mul]
  have hA : (A L m)^2 = 2^((7*L+m)*2) := by
    simp only [A,AdaptiveBitBounds.highInputBudget,Nat.mul_one,← Nat.pow_mul]
  have hq : q < 2^(q.log2+1) := (Nat.log2_lt (NeZero.ne q)).mp (by omega)
  have hbound : 5^(2*L+1)*(q*(A L m)^2) < 2^(25*L+q.log2+10) := by
    rw [hA]
    calc
      _ ≤ 2^(3*(2*L+1))*(q*2^((7*L+m)*2)) := Nat.mul_le_mul_right _ h5
      _ < 2^(3*(2*L+1))*(2^(q.log2+1)*2^((7*L+m)*2)) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right hq (by positivity)) (by positivity)
      _ = 2^(3*(2*L+1)+(q.log2+1)+(7*L+m)*2) := by rw [Nat.pow_add,Nat.pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hs := Nat.size_le.mpr hbound
  dsimp [S]
  omega


theorem arithmeticUnit_bound (width sizeParameter : ℕ)
    (hw : width ≤ 25*sizeParameter) (hS : 1 ≤ sizeParameter) :
    arithmeticUnit width ≤ 3000000*sizeParameter^2 := by
  have hwidth : width+1≤26*sizeParameter := by omega
  unfold arithmeticUnit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  calc
    _ = 800*(width+1)^2+8 := by ring
    _ ≤ 800*(26*sizeParameter)^2+8 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2)) _
    _ = 540800*sizeParameter^2+8 := by ring
    _ ≤ 540808*sizeParameter^2 := by
      have hp : 1 ≤ sizeParameter^2 := Nat.one_le_pow _ _ hS
      omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem high_arithmeticUnit_bound (L m q : ℕ) [NeZero q] (hm : m ≤ L) :
    arithmeticUnit (5^(2*L+1)*(q*(A L m)^2)).size ≤ 3000000*(S L q)^2 :=
  arithmeticUnit_bound _ _ (highEntry_size_bound L m q hm) (S_pos L q)


theorem baseCard_le_preprocessingWork (L m t : ℕ) :
    Fintype.card (BaseStates L m t) ≤ HighBoxDP.preprocessingWork L m t := by
  classical
  let embed : BaseStates L m t → States L m t :=
    fun w => ⟨w.val,w.property.1,fun i _ hi _ => (w.property.2 i hi).elim⟩
  have hinj : Function.Injective embed := by
    intro w v h
    apply Subtype.ext
    exact congrArg (fun x : States L m t => x.val) h
  have hcard := Fintype.card_le_of_injective embed hinj
  have hwork : Fintype.card (States L m t) ≤ HighBoxDP.preprocessingWork L m t := by
    unfold HighBoxDP.preprocessingWork
    calc
      _ = ∑ _w : States L m t, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro w _
        unfold HighBoxDP.stateWork
        split <;> omega
  exact hcard.trans hwork

theorem baseCard_mul_le_old (L m t q fullMultiply : ℕ) :
    Fintype.card (BaseStates L m t)*(q+fullMultiply) ≤
      ThinProductCosts.highPreprocessingCost L m t q 1 fullMultiply := by
  unfold ThinProductCosts.highPreprocessingCost ThinProductCosts.vectorUnit
  simp only [Nat.mul_one]
  apply Nat.mul_le_mul_right
  rw [HighBoxDP.scheduledWork_eq]
  exact (baseCard_le_preprocessingWork L m t).trans (Nat.le_add_right _ _)

/-- The binary preparation's metadata and scalar-bit overhead is only a
fixed polynomial over the old complete-vector HIGH cost. -/
theorem preparationBudget_le_old_seventh (L m t q : ℕ) [NeZero q] (hm : m ≤ L) :
    BinaryHighTable.preparationBudget L m t q (A L m) ≤
      16000000000*(S L q)^7*
        ThinProductCosts.highPreprocessingCost L m t q 1
          (BinaryMultiplierAdapter.workBound q (A L m)) := by
  have hF := highLayerFactor_bound L q
  have hU := high_arithmeticUnit_bound L m q hm
  have hB := baseBudget_bound L q (A L m)
  have hS := S_pos L q
  have hqV : q ≤ V q (A L m) := by unfold V; omega
  have hp : (S L q)^2 ≤ (S L q)^5 := Nat.pow_le_pow_right hS (by decide)
  have hbody :
      ArrayKeys.highLayerFactor L q 0*arithmeticUnit (5^(2*L+1)*(q*(A L m)^2)).size+
        baseBudget L q (A L m) ≤ 4000000000*(S L q)^5*V q (A L m) := by
    calc
      _ ≤ (1000*(S L q)^3*q)*(3000000*(S L q)^2)+100*(S L q)^2*V q (A L m) :=
        Nat.add_le_add (Nat.mul_le_mul hF hU) hB
      _ = 3000000000*(S L q)^5*q+100*(S L q)^2*V q (A L m) := by ring
      _ ≤ 3000000000*(S L q)^5*V q (A L m)+100*(S L q)^5*V q (A L m) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hqV)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp))
      _ = 3000000100*(S L q)^5*V q (A L m) := by ring
      _ ≤ _ := by gcongr; norm_num
  have houter : (2*L+1)^2 ≤ 4*(S L q)^2 := by
    have h : 2*L+1 ≤ 2*S L q := by dsimp [S]; omega
    have hp := Nat.pow_le_pow_left h 2
    simpa [mul_pow] using hp
  have hcost := baseCard_mul_le_old L m t q (BinaryMultiplierAdapter.workBound q (A L m))
  unfold BinaryHighTable.preparationBudget
  calc
    _ ≤ (4*(S L q)^2)*Fintype.card (BaseStates L m t)*
        (4000000000*(S L q)^5*V q (A L m)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ houter) hbody
    _ = 16000000000*(S L q)^7*(Fintype.card (BaseStates L m t)*V q (A L m)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcost


/-- Explicit generous collector envelope requested by the binary backend. -/
theorem preparationBudget_le_old (L m t q : ℕ) [NeZero q] (hm : m ≤ L) :
    BinaryHighTable.preparationBudget L m t q (AdaptiveBitBounds.highInputBudget L m 1) ≤
      100000000000000000000*(L+q.log2+1)^12*
        ThinProductCosts.highPreprocessingCost L m t q 1
          (BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)) := by
  have hS := S_pos L q
  have hp : (S L q)^7 ≤ (S L q)^12 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ 16000000000*(S L q)^7*
        ThinProductCosts.highPreprocessingCost L m t q 1
          (BinaryMultiplierAdapter.workBound q (A L m)) := preparationBudget_le_old_seventh L m t q hm
    _ ≤ 16000000000*(S L q)^12*
        ThinProductCosts.highPreprocessingCost L m t q 1
          (BinaryMultiplierAdapter.workBound q (A L m)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ ≤ _ := by gcongr; norm_num


theorem baseCount_pos (L m t : ℕ) : 1 ≤ Fintype.card (BaseStates L m t) := by
  let z : BaseStates L m t := ⟨CappedEnumeration.zeroWord (2*L),
    (StoredHighDP.high_zero L m t).1,by intro i; simp [CappedEnumeration.zeroWord]⟩
  letI : Nonempty (BaseStates L m t) := ⟨z⟩
  exact Fintype.card_pos

theorem highPreprocessingCost_pos (L m t q fullMultiply : ℕ) [NeZero q] :
    1 ≤ ThinProductCosts.highPreprocessingCost L m t q 1 fullMultiply := by
  have hb := baseCount_pos L m t
  have hq : 1≤q+fullMultiply := by have := NeZero.pos q; omega
  have hp : 1 ≤ Fintype.card (BaseStates L m t)*(q+fullMultiply) := Nat.mul_pos hb hq
  exact hp.trans (baseCard_mul_le_old L m t q fullMultiply)

/-- The same generous envelope also absorbs the collector's fixed charge. -/
theorem preparationBudget_add_eight_le_old (L m t q : ℕ) [NeZero q] (hm : m ≤ L) :
    BinaryHighTable.preparationBudget L m t q (AdaptiveBitBounds.highInputBudget L m 1)+8 ≤
      100000000000000000000*(L+q.log2+1)^12*
        ThinProductCosts.highPreprocessingCost L m t q 1
          (BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)) := by
  let cost := ThinProductCosts.highPreprocessingCost L m t q 1
    (BinaryMultiplierAdapter.workBound q (A L m))
  have hc : 1≤cost := highPreprocessingCost_pos L m t q _
  have hS := S_pos L q
  have hs7 : 1≤(S L q)^7 := Nat.one_le_pow _ _ hS
  have h8 : 8≤8*((S L q)^7*cost) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hs7 hc)
  have hp : (S L q)^7≤(S L q)^12 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ 16000000000*(S L q)^7*cost+8*((S L q)^7*cost) :=
      Nat.add_le_add (preparationBudget_le_old_seventh L m t q hm) h8
    _ = 16000000008*(S L q)^7*cost := by ring
    _ ≤ 16000000008*(S L q)^12*cost := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ ≤ _ := by gcongr; norm_num

#print axioms fftWork_le_adapter
#print axioms highLayerFactor_bound
#print axioms baseBudget_bound
#print axioms highEntry_size_bound
#print axioms high_arithmeticUnit_bound
#print axioms baseCard_mul_le_old
#print axioms preparationBudget_le_old
#print axioms highPreprocessingCost_pos
#print axioms preparationBudget_le_old_seventh
#print axioms preparationBudget_add_eight_le_old
#print axioms preparationBudget_le_old
end ThinMatrix.BinaryHighBudget

namespace ThinMatrix.BinaryGeometryWidth
open AdaptiveBitBounds

def geometryWidth (L m q : ℕ) : ℕ :=
  9*(100*L+106*m+q.size+103+2*(4*m+2)^2+20)

theorem inflation_constant (cL cm cq : ℕ) :
    9*(100*cL+106*cm+cq+124+2*(4*cm+2)^2) ≤
      CoefficientBudget.budgetConstant (9*cL+9) (9*cm+9) (9*cq+9) 0+
        2*(4*(9*cm+9)+2)^2+20 := by
  unfold CoefficientBudget.budgetConstant
  ring_nf
  omega

theorem geometryWidth_le_common (n L m q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    geometryWidth L m q ≤ commonBitWidth n 0 (9*cL+9) (9*cm+9) (9*cq+9) := by
  let r := n.size
  let R := (r+1)^2
  let A := 100*cL+106*cm+cq
  have hqsize : q.size ≤ cq*r+1 := (Nat.size_le_size hq).trans_eq Nat.size_pow
  have hrR : r ≤ R := by dsimp [R]; nlinarith
  have hR : 1 ≤ R := Nat.one_le_pow _ _ (by omega)
  have hlinear : 100*L+106*m+q.size+123 ≤ A*r+124 := by
    have hl := Nat.mul_le_mul_left 100 hL
    have hm' := Nat.mul_le_mul_left 106 hm
    change 100*L ≤ 100*(cL*r) at hl
    change 106*m ≤ 106*(cm*r) at hm'
    calc
      _ ≤ 100*(cL*r)+106*(cm*r)+(cq*r+1)+123 := by omega
      _ = _ := by dsimp [A]; ring
  have hlin : 100*L+106*m+q.size+123 ≤ (A+124)*R := by
    calc
      _ ≤ A*r+124 := hlinear
      _ ≤ A*R+124*R := Nat.add_le_add (Nat.mul_le_mul_left A hrR)
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 124 hR)
      _ = _ := by ring
  have hcap : 4*m+2 ≤ (4*cm+2)*(r+1) := by
    have hm' := Nat.mul_le_mul_left 4 hm
    change 4*m ≤ 4*(cm*r) at hm'
    ring_nf at hm' ⊢
    omega
  have hsquare := Nat.pow_le_pow_left hcap 2
  rw [mul_pow] at hsquare
  have hfactor : 2*(4*m+2)^2 ≤ (2*(4*cm+2)^2)*R := by
    exact (Nat.mul_le_mul_left 2 hsquare).trans_eq (by dsimp [R]; ring)
  have hsum : 100*L+106*m+q.size+123+2*(4*m+2)^2 ≤
      (A+124+2*(4*cm+2)^2)*R := by
    exact (Nat.add_le_add hlin hfactor).trans_eq (by ring)
  have htotal := Nat.mul_le_mul_left 9 hsum
  have hc := Nat.mul_le_mul_right R (inflation_constant cL cm cq)
  change geometryWidth L m q ≤
    (CoefficientBudget.budgetConstant (9*cL+9) (9*cm+9) (9*cq+9) 0+
      2*(4*(9*cm+9)+2)^2+20)*R
  calc
    geometryWidth L m q = 9*(100*L+106*m+q.size+123+2*(4*m+2)^2) := by
      unfold geometryWidth
      omega
    _ ≤ 9*((A+124+2*(4*cm+2)^2)*R) := htotal
    _ = (9*(100*cL+106*cm+cq+124+2*(4*cm+2)^2))*R := by dsimp [A]; ring
    _ ≤ _ := hc

#print axioms inflation_constant
#print axioms geometryWidth_le_common
end ThinMatrix.BinaryGeometryWidth


namespace ThinMatrix.BinaryBackendCosts
open scoped BigOperators
open BinaryBackendExecution ThinMatrixBackend CoefficientBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
noncomputable section

def lowFactor (n degree cL cm cq : ℕ) : ℕ :=
  (1600*(BinaryLowEncoder.scalarConstant degree cL cm cq+1)^2+6*cL+3)*(n.size+1)^4

def bandAllowance (n degree L m t q cL cm cq : ℕ) : ℕ :=
  BinaryBandSource.preparationBudget L m q 1+
    (2*m+1)*(CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1))*
      lowFactor n degree cL cm cq+8*(2*m+1)

theorem coefficient_size_one {z : ℤ} (hz : z.natAbs ≤ 1) : z.natAbs.size ≤ 1 := by
  exact (Nat.size_le_size hz).trans_eq (by decide)

theorem prepareLeftBand_price {L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : BinaryBandSource.StoredLeftMatrix L m q)
    (hd : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs ≤ 1)
    (n degree cL cm cq : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    (BinaryBackendExecution.prepareLeftBand (t := t)
      (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) shape data).bitSteps ≤
      bandAllowance n degree L m t q cL cm cq := by
  have hs := BinaryBandSource.prepareLeft_cost shape data 1
    (fun a r => coefficient_size_one (hd a r)) hmL
  have hl (i : Fin (2*m+1)) :
      (BinaryLowEncoder.prepareRawSource (m := m) (t := t)
        (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) true
        ((BinaryBandSource.prepareLeft shape data).runs.get i)).bitSteps ≤
      (CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1))*
        lowFactor n degree cL cm cq := by
    have h := BinaryLowEncoder.source_prepareRaw_polylog (A := 1) (by decide) true _
      (BinaryBandBounds.left_source_coeffBound shape data hd i) n degree cL cm cq
      hL hm hq (Nat.one_le_pow _ _ hn) ht
    have hc := CacheDenseLowering.prepareSource_work_le (m := m) (t := t) (q := q)
      (width := 2*m+1) (by omega) true
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw ((BinaryBandSource.prepareLeft shape data).runs.get i)))
    apply h.trans
    simpa only [lowFactor,Nat.mul_assoc] using
      Nat.mul_le_mul_right (lowFactor n degree cL cm cq) hc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  simp only [BinaryBackendExecution.prepareLeftBand,Vector.get_map]
  change (BinaryBandSource.prepareLeft shape data).operations+
    (∑ i : Fin (2*m+1), (BinaryLowEncoder.prepareRawSource (m := m) (t := t)
      (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) true
      ((BinaryBandSource.prepareLeft shape data).runs.get i)).bitSteps)+8*(2*m+1) ≤ _
  unfold bandAllowance
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.add_le_add hs hsum) (8*(2*m+1))

theorem prepareRightBand_price {L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (data : BinaryBandSource.StoredRightMatrix L m q)
    (hd : ∀ a r, (BinaryCell.view ((data.get a).get r)).natAbs ≤ 1)
    (n degree cL cm cq : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    (BinaryBackendExecution.prepareRightBand (t := t)
      (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) shape data).bitSteps ≤
      bandAllowance n degree L m t q cL cm cq := by
  have hs := BinaryBandSource.prepareRight_cost shape data 1
    (fun a r => coefficient_size_one (hd a r)) hmL
  have hl (i : Fin (2*m+1)) :
      (BinaryLowEncoder.prepareRawSource (m := m) (t := t)
        (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) false
        ((BinaryBandSource.prepareRight shape data).runs.get i)).bitSteps ≤
      (CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1))*
        lowFactor n degree cL cm cq := by
    have h := BinaryLowEncoder.source_prepareRaw_polylog (A := 1) (by decide) false _
      (BinaryBandBounds.right_source_coeffBound shape data hd i) n degree cL cm cq
      hL hm hq (Nat.one_le_pow _ _ hn) ht
    have hc := CacheDenseLowering.prepareSource_work_le (m := m) (t := t) (q := q)
      (width := 2*m+1) (by omega) false
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw ((BinaryBandSource.prepareRight shape data).runs.get i)))
    apply h.trans
    simpa only [lowFactor,Nat.mul_assoc] using
      Nat.mul_le_mul_right (lowFactor n degree cL cm cq) hc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  simp only [BinaryBackendExecution.prepareRightBand,Vector.get_map]
  change (BinaryBandSource.prepareRight shape data).operations+
    (∑ i : Fin (2*m+1), (BinaryLowEncoder.prepareRawSource (m := m) (t := t)
      (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) false
      ((BinaryBandSource.prepareRight shape data).runs.get i)).bitSteps)+8*(2*m+1) ≤ _
  unfold bandAllowance
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.add_le_add hs hsum) (8*(2*m+1))

def highAllowance (L m t q : ℕ) : ℕ :=
  2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L*q*
    HighBaseEncoder.baseCount L m t+
    BinaryHighTable.preparationBudget L m t q (AdaptiveBitBounds.highInputBudget L m 1)+8

theorem source_to_operand_cap (L m : ℕ) :
    8^(2*L)*2^(L+m) = AdaptiveBitBounds.highInputBudget L m 1 := by
  unfold AdaptiveBitBounds.highInputBudget
  simp only [Nat.mul_one]
  rw [show (8:ℕ)=2^3 by norm_num,←pow_mul,←pow_add]
  congr 1
  omega

theorem prepareHigh_price {L m t q : ℕ} [NeZero q]
    (X Y : BinarySourceFormation.RawStore L q)
    (hX : BinaryHighExecution.RawBound X (2^(L+m)))
    (hY : BinaryHighExecution.RawBound Y (2^(L+m))) :
    (BinaryBackendExecution.prepareHigh (L := L) (m := m) (t := t) 1 X Y).bitSteps ≤
      highAllowance L m t q := by
  have hl := BinaryHighCost.encodeRawSource_bit_price L m t q (2^(L+m)) true X hX NeZero.one_le
  have hr := BinaryHighCost.encodeRawSource_bit_price L m t q (2^(L+m)) false Y hY NeZero.one_le
  have hnl := HighBaseEncoder.encodeVector_work (m := m) (t := t) true (SourceCoordinates.leftForms L)
    (SourceCoordinates.leftVectorInput (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw X))) NeZero.one_le
  have hnr := HighBaseEncoder.encodeVector_work (m := m) (t := t) false (SourceCoordinates.rightForms L)
    (SourceCoordinates.rightVectorInput (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw Y))) NeZero.one_le
  change _ ≤ BackendCostRefinement.highEncodingFactor L*q*HighBaseEncoder.baseCount L m t at hnl hnr
  dsimp only at hl hr
  have hl' := hl.trans (Nat.mul_le_mul_left _ hnl)
  have hr' := hr.trans (Nat.mul_le_mul_left _ hnr)
  have hx (w : HighBoxDP.BaseStates L m t) :=
    BinaryHighCost.encodeRawSource_readBase_bound L m t q (2^(L+m)) true X hX w
  have hy (w : HighBoxDP.BaseStates L m t) :=
    BinaryHighCost.encodeRawSource_readBase_bound L m t q (2^(L+m)) false Y hY w
  rw [source_to_operand_cap] at hx hy
  have hh := BinaryHighTable.prepare_work (L := L) (m := m) (t := t)
    (AdaptiveBitBounds.highInputBudget L m 1) (AdaptiveBitBounds.highInputBudget_pos L m 1 (by decide)) _ _ hx hy
  change (BinaryHighExecution.encodeRawSource L m t q true X).bitSteps+
    (BinaryHighExecution.encodeRawSource L m t q false Y).bitSteps+
    (BinaryHighTable.prepare (L := L) (m := m) (t := t)
      (AdaptiveBitBounds.highInputBudget L m 1)
      (BinaryHighExecution.encodeRawSource L m t q true X).table
      (BinaryHighExecution.encodeRawSource L m t q false Y).table).work+8 ≤ _
  unfold highAllowance
  have hsum := Nat.add_le_add (Nat.add_le_add hl' hr') hh
  exact (Nat.add_le_add_right hsum 8).trans_eq (by ring)


def bandFactor (n degree L m cL cm cq : ℕ) : ℕ :=
  BinarySourceFactor.sourceFactor L m+lowFactor n degree cL cm cq+8

theorem bandAllowance_native (n degree L m t q cL cm cq : ℕ) (hm : m ≤ L) (hq : 1 ≤ q) :
    bandAllowance n degree L m t q cL cm cq ≤
      bandFactor n degree L m cL cm cq*BackendCostRefinement.bandBudget L m t q := by
  have hs := BinarySourceFactor.preparationBudget_one L m q hm hq
  have hsp : 1 ≤ SourceFormation.sourceBudget L m (L-m) q (BackendCostRefinement.SourceCosts.readerBudget L m) := by
    have hp : 0 < SourceFormation.sourceBudget L m (L-m) q (BackendCostRefinement.SourceCosts.readerBudget L m) := by
      unfold SourceFormation.sourceBudget SourceFormation.wordBudget SourceFormation.metadataCost
      positivity
    omega
  have hsr : 2*m+1 ≤ BackendCostRefinement.bandSourceBudget L m q := by
    have hh := Nat.mul_le_mul_left (2*m+1) hsp
    unfold BackendCostRefinement.bandSourceBudget
    omega
  have hsource : BackendCostRefinement.bandSourceBudget L m q ≤ BackendCostRefinement.bandBudget L m t q := by
    unfold BackendCostRefinement.bandBudget
    omega
  have hlow : (2*m+1)*(CacheBounds.retainedLeafCount L m t*CachedLowQuery.preparationFactor L q (2*m+1)) ≤
      BackendCostRefinement.bandBudget L m t q := by
    unfold BackendCostRefinement.bandBudget
    rw [Nat.mul_assoc]
    omega
  have hhs := hs.trans (Nat.mul_le_mul_left _ hsource)
  have hhl := Nat.mul_le_mul_right (lowFactor n degree cL cm cq) hlow
  have hhc := Nat.mul_le_mul_left 8 (hsr.trans hsource)
  unfold bandAllowance bandFactor
  nlinarith

def bandConstant (degree cL cm cq : ℕ) : ℕ :=
  20000000*(2*cL+3)^3+1600*(BinaryLowEncoder.scalarConstant degree cL cm cq+1)^2+6*cL+11

theorem bandFactor_polylog (n degree L m cL cm cq : ℕ) (hL : L ≤ cL*n.size) :
    bandFactor n degree L m cL cm cq ≤ bandConstant degree cL cm cq*(n.size+1)^4 := by
  have hs := BinarySourceFactor.sourceFactor_polynomial n L m cL
    (hL.trans (Nat.mul_le_mul_left _ (by omega)))
  have hp : (n.size+1)^3 ≤ (n.size+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (n.size+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hs' := hs.trans (Nat.mul_le_mul_left _ hp)
  unfold bandFactor bandConstant lowFactor
  nlinarith

theorem prepareTile_price {L m t q : ℕ} [NeZero q]
    (shape : ShapePlan L m) (left : BinaryBandSource.StoredLeftMatrix L m q)
    (right : BinaryBandSource.StoredRightMatrix L m q) (W : ℕ)
    (hl : ∀ a r, (BinaryCell.view ((left.get a).get r)).natAbs ≤ 1)
    (hr : ∀ a r, (BinaryCell.view ((right.get a).get r)).natAbs ≤ 1) :
    (BinaryBackendExecution.prepareTile (t := t) 1
      (BinaryBackendExecution.prepareLeftBand (t := t) W shape left)
      (BinaryBackendExecution.prepareRightBand (t := t) W shape right)).bitSteps ≤
      (2*m+1)*highAllowance L m t q+8*(2*m+1) := by
  have hx (i : Fin (2*m+1)) : BinaryHighExecution.RawBound
      ((BinaryBandSource.prepareLeft shape left).runs.get i) (2^(L+m)) := by
    simpa only [Nat.mul_one] using BinaryLowEncoder.rawBound_of_sourceBound _
      (BinaryBandBounds.left_source_coeffBound shape left hl i)
  have hy (i : Fin (2*m+1)) : BinaryHighExecution.RawBound
      ((BinaryBandSource.prepareRight shape right).runs.get i) (2^(L+m)) := by
    simpa only [Nat.mul_one] using BinaryLowEncoder.rawBound_of_sourceBound _
      (BinaryBandBounds.right_source_coeffBound shape right hr i)
  have hp (i : Fin (2*m+1)) := prepareHigh_price (t := t) _ _ (hx i) (hy i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  simpa only [BinaryBackendExecution.prepareTile,BinaryBackendExecution.prepareLeftBand,
    BinaryBackendExecution.prepareRightBand,Vector.get_ofFn] using Nat.add_le_add_right hsum (8*(2*m+1))


theorem scalarUnit_mono {W V : ℕ} (h : W ≤ V) :
    BackendScalarBits.backendScalarUnit W ≤ BackendScalarBits.backendScalarUnit V := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

theorem prepareRawSource_bitSteps_mono {L m t q : ℕ} (side : Bool)
    (raw : BinarySourceFormation.RawStore L q) {W V : ℕ} (h : W ≤ V) :
    (BinaryLowEncoder.prepareRawSource (m := m) (t := t) W side raw).bitSteps ≤
      (BinaryLowEncoder.prepareRawSource (m := m) (t := t) V side raw).bitSteps := by
  have hu := scalarUnit_mono (Nat.add_le_add_right h 15)
  unfold BinaryLowEncoder.prepareRawSource BinaryLowEncoder.prepareVectors BinaryLowEncoder.bitWork
  dsimp only
  gcongr

theorem prepareLeftBand_bitSteps_mono {L m t q : ℕ} (shape : ShapePlan L m)
    (data : BinaryBandSource.StoredLeftMatrix L m q) {W V : ℕ} (h : W ≤ V) :
    (BinaryBackendExecution.prepareLeftBand (t := t) W shape data).bitSteps ≤
      (BinaryBackendExecution.prepareLeftBand (t := t) V shape data).bitSteps := by
  simp only [BinaryBackendExecution.prepareLeftBand,Vector.get_map]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum (fun i _ => prepareRawSource_bitSteps_mono true _ h)

theorem prepareRightBand_bitSteps_mono {L m t q : ℕ} (shape : ShapePlan L m)
    (data : BinaryBandSource.StoredRightMatrix L m q) {W V : ℕ} (h : W ≤ V) :
    (BinaryBackendExecution.prepareRightBand (t := t) W shape data).bitSteps ≤
      (BinaryBackendExecution.prepareRightBand (t := t) V shape data).bitSteps := by
  simp only [BinaryBackendExecution.prepareRightBand,Vector.get_map]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum (fun i _ => prepareRawSource_bitSteps_mono false _ h)

theorem commonBitWidth_pos (n degree cL cm cq : ℕ) :
    1 ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  unfold AdaptiveBitBounds.commonBitWidth
  have hsq : 1 ≤ (n.size+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hconst : 1 ≤ CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20 := by omega
  exact Nat.mul_pos hconst hsq


def fullBudget (L m q : ℕ) : ℕ :=
  BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)

def nativeHigh (L m t q : ℕ) : ℕ := ThinProductCosts.highPreprocessingCost L m t q 1 (fullBudget L m q)

def highFactor (L m q : ℕ) : ℕ :=
  2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L+
    100000000000000000000*(L+q.log2+1)^12+8

theorem highAllowance_native (L m t q : ℕ) [NeZero q] (hm : m ≤ L) :
    highAllowance L m t q+8 ≤ highFactor L m q*nativeHigh L m t q := by
  have hcard := BinaryHighBudget.baseCard_mul_le_old L m t q (fullBudget L m q)
  have hbase : HighBaseEncoder.baseCount L m t*q ≤ nativeHigh L m t q := by
    apply (Nat.mul_le_mul_left (HighBaseEncoder.baseCount L m t) (show q ≤ q+fullBudget L m q by omega)).trans
    exact hcard
  have henc := Nat.mul_le_mul_left
    (2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L) hbase
  have hdp := BinaryHighBudget.preparationBudget_add_eight_le_old L m t q hm
  have hp : 1 ≤ nativeHigh L m t q := BinaryHighBudget.highPreprocessingCost_pos L m t q _
  have h8 := Nat.mul_le_mul_left 8 hp
  calc
    _ = (2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L)*
        (HighBaseEncoder.baseCount L m t*q)+
        (BinaryHighTable.preparationBudget L m t q (AdaptiveBitBounds.highInputBudget L m 1)+8)+8 := by
      unfold highAllowance
      ring
    _ ≤ (2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L)*nativeHigh L m t q+
        (100000000000000000000*(L+q.log2+1)^12)*nativeHigh L m t q+8*nativeHigh L m t q :=
      Nat.add_le_add (Nat.add_le_add henc hdp) (by simpa only [Nat.mul_one] using h8)
    _ = _ := by unfold highFactor; rw [Nat.add_mul,Nat.add_mul]

def highConstant (cL cm cq : ℕ) : ℕ :=
  600*(10000000*(2*cL+2)^3*(7*cL+cm+12)^2)*(cL+1)^2+
    100000000000000000000*(cL+cq+2)^12+8

private theorem scaled_product (a b r : ℕ) :
    2*(a*r^5)*(300*(b*r)^2) = 600*a*b^2*r^7 := by ring

attribute [local irreducible] highFactor highConstant

theorem highFactor_polylog (n L m q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    highFactor L m q ≤ highConstant cL cm cq*(n.size+1)^12 := by
  unfold highFactor
  have hraw := BinaryHighPolylog.rawStoredFactor_polylog L m n cL cm hL hm
  have henc := BackendCostRefinement.highEncodingFactor_le L
  have hL1 : L+1 ≤ (cL+1)*(n.size+1) := by
    nlinarith only [hL, Nat.zero_le cL, Nat.zero_le n.size]
  have hsq := Nat.pow_le_pow_left hL1 2
  have hproduct := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hraw)
    (henc.trans (Nat.mul_le_mul_left 300 hsq))
  have he : 2*BinaryHighCost.rawStoredFactor L (2^(L+m))*BackendCostRefinement.highEncodingFactor L ≤
      600*(10000000*(2*cL+2)^3*(7*cL+cm+12)^2)*(cL+1)^2*(n.size+1)^7 := by
    exact hproduct.trans_eq (scaled_product
      (10000000*(2*cL+2)^3*(7*cL+cm+12)^2) (cL+1) (n.size+1))
  have hqsize := (Nat.size_le_size hq).trans_eq Nat.size_pow
  have hqlog := BinaryMultiplierAdapter.log2_le_size q
  have hS : L+q.log2+1 ≤ (cL+cq+2)*(n.size+1) := by
    nlinarith only [hL,hqsize,hqlog,Nat.zero_le cL,Nat.zero_le cq,Nat.zero_le n.size]
  have hpow := Nat.pow_le_pow_left hS 12
  rw [mul_pow] at hpow
  have h7 : (n.size+1)^7 ≤ (n.size+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have he' := he.trans (Nat.mul_le_mul_left _ h7)
  have hdp : 100000000000000000000*(L+q.log2+1)^12 ≤
      (100000000000000000000*(cL+cq+2)^12)*(n.size+1)^12 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 100000000000000000000 hpow
  have hp : 1 ≤ (n.size+1)^12 := Nat.one_le_pow _ _ (by omega)
  have h8 := Nat.mul_le_mul_left 8 hp
  calc
    _ ≤ (600*(10000000*(2*cL+2)^3*(7*cL+cm+12)^2)*(cL+1)^2)*(n.size+1)^12+
        (100000000000000000000*(cL+cq+2)^12)*(n.size+1)^12+8*(n.size+1)^12 :=
      Nat.add_le_add (Nat.add_le_add he' hdp) (by simpa only [Nat.mul_one] using h8)
    _ = _ := by unfold highConstant; rw [Nat.add_mul,Nat.add_mul]


def copyAllowance (L m q : ℕ) : ℕ :=
  ((BackendScalarBits.backendScalarUnit 1+9)*q+24)*(tileWidth L m*4^m)

def globalAllowance (shapeOps n degree N L m t q cL cm cq : ℕ) : ℕ :=
  let R := TilingCosts.bandCount N (tileWidth L m)
  shapeOps+2*R*copyAllowance L m q+2*R*bandAllowance n degree L m t q cL cm cq+
    R^2*((2*m+1)*(highAllowance L m t q+8))+32*R

theorem global_leftData {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (left : BinaryBackendExecution.OriginalLeft N D q) (right : BinaryBackendExecution.OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    ((BinaryBackendExecution.prepareGlobalShape (t := t) shape W A left right).leftData.get b) =
      BinaryBackendExecution.makeLeftBandStored shape left b.val := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [BinaryBackendExecution.prepareGlobalShape,Vector.cast_rfl]

theorem global_rightData {N D L m t q : ℕ} (shape : ShapePlan L m) (W A : ℕ)
    (left : BinaryBackendExecution.OriginalLeft N D q) (right : BinaryBackendExecution.OriginalRight N D q)
    (b : Fin (TilingCosts.bandCount N (tileWidth L m))) :
    ((BinaryBackendExecution.prepareGlobalShape (t := t) shape W A left right).rightData.get b) =
      BinaryBackendExecution.makeRightBandStored shape right b.val := by
  rcases shape with ⟨env,layout,hgood,hgamma,hdelta,hcols,width,hwidth,operations⟩
  subst width
  simp [BinaryBackendExecution.prepareGlobalShape,Vector.cast_rfl]

/-- The actual global execution is priced from its original zero/one cells.
Both band families and the entire square array of tiles remain explicit. -/
theorem prepareGlobalShape_price {N D L m t q : ℕ} [NeZero q] (shape : ShapePlan L m)
    (left : BinaryBackendExecution.OriginalLeft N D q) (right : BinaryBackendExecution.OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1)
    (n degree cL cm cq W : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m)
    (hW : W ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq) :
    (BinaryBackendExecution.prepareGlobalShape (t := t) shape W 1 left right).bitSteps ≤
      globalAllowance shape.operations n degree N L m t q cL cm cq := by
  let p := BinaryBackendExecution.prepareGlobalShape (t := t) shape W 1 left right
  let R := TilingCosts.bandCount N (tileWidth L m)
  have hleft (b : Fin R) := BinaryBandCopyBounds.makeLeftBandStored_natAbs shape left b.val hl
  have hright (b : Fin R) := BinaryBandCopyBounds.makeRightBandStored_natAbs shape right b.val hr
  have hcl (b : Fin R) : (p.leftData.get b).operations ≤ copyAllowance L m q := by
    rw [global_leftData]
    have h := BinaryBandCopyBounds.makeLeftBandStored_price shape left b.val hl
    simpa only [copyAllowance,shape.width_eq,show (1 : ℕ).size = 1 by decide] using h
  have hcr (b : Fin R) : (p.rightData.get b).operations ≤ copyAllowance L m q := by
    rw [global_rightData]
    have h := BinaryBandCopyBounds.makeRightBandStored_price shape right b.val hr
    rw [shape.width_eq,show (1 : ℕ).size = 1 by decide] at h
    convert h using 1
    unfold copyAllowance
    ring
  have hbl (b : Fin R) : (p.left.get b).bitSteps ≤ bandAllowance n degree L m t q cL cm cq := by
    rw [BinaryBackendExecution.prepareGlobalShape_left]
    exact (prepareLeftBand_bitSteps_mono shape _ hW).trans
      (prepareLeftBand_price shape _ (hleft b) n degree cL cm cq hn hmL hL hm hq ht)
  have hbr (b : Fin R) : (p.right.get b).bitSteps ≤ bandAllowance n degree L m t q cL cm cq := by
    rw [BinaryBackendExecution.prepareGlobalShape_right]
    exact (prepareRightBand_bitSteps_mono shape _ hW).trans
      (prepareRightBand_price shape _ (hright b) n degree cL cm cq hn hmL hL hm hq ht)
  have hbt (b c : Fin R) : ((p.tiles.get b).get c).bitSteps ≤
      (2*m+1)*(highAllowance L m t q+8) := by
    rw [BinaryBackendExecution.prepareGlobalShape_tile]
    convert prepareTile_price (t := t) shape _ _ W (hleft b) (hright c) using 1
    ring
  have hscl := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hcl b)
  have hscr := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hcr b)
  have hsbl := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hbl b)
  have hsbr := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hbr b)
  have hsbt := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun c _ => hbt b c))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hscl hscr hsbl hsbr hsbt
  have he := BinaryBackendExecution.prepareGlobalShape_work (t := t) shape W 1 left right
  change p.bitSteps = _ at he
  rw [he]
  unfold globalAllowance
  change _ ≤ shape.operations+2*R*copyAllowance L m q+2*R*bandAllowance n degree L m t q cL cm cq+
    R^2*((2*m+1)*(highAllowance L m t q+8))+32*R
  calc
    _ ≤ shape.operations+R*copyAllowance L m q+R*copyAllowance L m q+
        R*bandAllowance n degree L m t q cL cm cq+R*bandAllowance n degree L m t q cL cm cq+
        R*(R*((2*m+1)*(highAllowance L m t q+8)))+32*R :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add_left hscl shape.operations) hscr) hsbl) hsbr) hsbt) (32*R)
    _ = _ := by ring


def preparationFactor (n degree L m q cL cm cq : ℕ) : ℕ :=
  1001+bandFactor n degree L m cL cm cq+highFactor L m q

def nativeShapeAllowance (shapeOps N L m t q : ℕ) : ℕ :=
  let R := TilingCosts.bandCount N (tileWidth L m)
  shapeOps+20*q*R*tileWidth L m*4^m+2*R*BackendCostRefinement.bandBudget L m t q+
    R^2*((2*m+1)*3000*(L+1)^5*nativeHigh L m t q)

theorem copyAllowance_le (L m q : ℕ) (hq : 1 ≤ q) :
    copyAllowance L m q ≤ 3233*q*(tileWidth L m*4^m) := by
  have hc : (BackendScalarBits.backendScalarUnit 1+9)*q+24 ≤ 3233*q := by
    norm_num [BackendScalarBits.backendScalarUnit,BackendScalarBits.scalarUnit]
    omega
  exact Nat.mul_le_mul_right _ hc

theorem globalAllowance_native (shapeOps n degree N L m t q cL cm cq : ℕ)
    [NeZero q] (hm : m ≤ L) :
    globalAllowance shapeOps n degree N L m t q cL cm cq ≤
      preparationFactor n degree L m q cL cm cq*nativeShapeAllowance shapeOps N L m t q := by
  let R := TilingCosts.bandCount N (tileWidth L m)
  let F := preparationFactor n degree L m q cL cm cq
  let cell := tileWidth L m*4^m
  have hq : 1 ≤ q := NeZero.one_le
  have hcell : 1 ≤ cell := Nat.mul_pos (tileWidth_pos L m hm) (Nat.one_le_pow _ _ (by norm_num))
  have hF : 1 ≤ F := by dsimp [F,preparationFactor]; omega
  have hFc : 1000 ≤ F := by dsimp [F,preparationFactor]; omega
  have hFb : bandFactor n degree L m cL cm cq ≤ F := by dsimp [F,preparationFactor]; omega
  have hFh : highFactor L m q ≤ F := by dsimp [F,preparationFactor]; omega
  have hcopy := copyAllowance_le L m q hq
  have h32 : 32 ≤ 32*(q*cell) := Nat.mul_le_mul_left 32 (Nat.mul_pos hq hcell)
  have hcopy0 : 2*copyAllowance L m q+32 ≤ 1000*(20*q*cell) := by
    change copyAllowance L m q ≤ 3233*q*cell at hcopy
    nlinarith
  have hcopyR := Nat.mul_le_mul_left R hcopy0
  have hcopyF := Nat.mul_le_mul_right (20*q*R*cell) hFc
  have hcopies : 2*R*copyAllowance L m q+32*R ≤ F*(20*q*R*cell) := by
    apply (show 2*R*copyAllowance L m q+32*R ≤ 1000*(20*q*R*cell) by
      convert hcopyR using 1 <;> ring).trans hcopyF
  have hband := bandAllowance_native n degree L m t q cL cm cq hm hq
  have hb := Nat.mul_le_mul_left (2*R) (hband.trans
    (Nat.mul_le_mul_right (BackendCostRefinement.bandBudget L m t q) hFb))
  have hhigh := highAllowance_native L m t q hm
  have hh := Nat.mul_le_mul_left (R^2*(2*m+1)) (hhigh.trans
    (Nat.mul_le_mul_right (nativeHigh L m t q) hFh))
  have hK : 1 ≤ 3000*(L+1)^5 := by
    have hp : 1 ≤ (L+1)^5 := Nat.one_le_pow _ _ (by omega)
    omega
  have hbig : nativeHigh L m t q ≤ 3000*(L+1)^5*nativeHigh L m t q :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hh' := hh.trans (Nat.mul_le_mul_left (R^2*(2*m+1)) (Nat.mul_le_mul_left F hbig))
  have hshape : shapeOps ≤ F*shapeOps := Nat.le_mul_of_pos_left _ (by omega)
  unfold globalAllowance nativeShapeAllowance
  change shapeOps+2*R*copyAllowance L m q+2*R*bandAllowance n degree L m t q cL cm cq+
      R^2*((2*m+1)*(highAllowance L m t q+8))+32*R ≤
    F*(shapeOps+20*q*R*tileWidth L m*4^m+2*R*BackendCostRefinement.bandBudget L m t q+
      R^2*((2*m+1)*3000*(L+1)^5*nativeHigh L m t q))
  calc
    _ = shapeOps+(2*R*copyAllowance L m q+32*R)+2*R*bandAllowance n degree L m t q cL cm cq+
        (R^2*(2*m+1))*(highAllowance L m t q+8) := by ring
    _ ≤ F*shapeOps+F*(20*q*R*cell)+
        (2*R)*(F*BackendCostRefinement.bandBudget L m t q)+
        (R^2*(2*m+1))*(F*(3000*(L+1)^5*nativeHigh L m t q)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hshape hcopies) hb) hh'
    _ = _ := by dsimp [cell]; ring

def preparationConstant (degree cL cm cq : ℕ) : ℕ :=
  1001+bandConstant degree cL cm cq+highConstant cL cm cq

theorem preparationFactor_polylog (n degree L m q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    preparationFactor n degree L m q cL cm cq ≤ preparationConstant degree cL cm cq*(n.size+1)^12 := by
  have hb := bandFactor_polylog n degree L m cL cm cq hL
  have hp : (n.size+1)^4 ≤ (n.size+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hb' := hb.trans (Nat.mul_le_mul_left _ hp)
  have hh := highFactor_polylog n L m q cL cm cq hL hm hq
  have hpos : 1 ≤ (n.size+1)^12 := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left 1001 hpos
  unfold preparationFactor preparationConstant
  exact (Nat.add_le_add (Nat.add_le_add (by simpa only [Nat.mul_one] using hc) hb') hh).trans_eq
    (by rw [Nat.add_mul,Nat.add_mul])


/-- Closed entry-point price. The multiplier allowance is the actual binary
FFT budget at the derived original-source operand cap. -/
theorem prepareGlobal_price {N D L m t q : ℕ} [NeZero q]
    (left : BinaryBackendExecution.OriginalLeft N D q)
    (right : BinaryBackendExecution.OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1)
    (n degree cL cm cq W : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m)
    (hW : W ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq) :
    (BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t) W 1 left right).bitSteps ≤
      preparationConstant degree cL cm cq*(n.size+1)^12*
        BackendCostRefinement.globalPreparationBudget N L m t q (fullBudget L m q) := by
  have hp := prepareGlobalShape_price (BinaryBackendExecution.prepareShapeRuntime L m)
    left right hl hr n degree cL cm cq W hn hmL hL hm hq ht hW
  have hnativ := globalAllowance_native
    (BinaryBackendExecution.prepareShapeRuntime L m).operations n degree N L m t q cL cm cq hmL
  have hfactor := preparationFactor_polylog n degree L m q cL cm cq hL hm hq
  have hc := hp.trans (hnativ.trans (Nat.mul_le_mul_right _ hfactor))
  simpa only [BinaryBackendExecution.prepareGlobal,
    BinaryBackendExecution.prepareShapeRuntime_refines,nativeShapeAllowance,
    BackendCostRefinement.globalPreparationBudget,nativeHigh] using hc


/-- Price the concrete geometry-only width, using only original zero/one
cells and linear logarithmic bounds on the public phase parameters. -/
theorem prepareGlobal_geometry_price {N D L m t q : ℕ} [NeZero q]
    (left : BinaryBackendExecution.OriginalLeft N D q)
    (right : BinaryBackendExecution.OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1)
    (n cL cm cq : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    (BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right).bitSteps ≤
      preparationConstant 0 (9*cL+9) (9*cm+9) (9*cq+9)*(n.size+1)^12*
        BackendCostRefinement.globalPreparationBudget N L m t q (fullBudget L m q) := by
  apply prepareGlobal_price left right hl hr n 0 (9*cL+9) (9*cm+9) (9*cq+9) _ hn hmL
  · exact hL.trans (Nat.mul_le_mul_right n.size (by omega))
  · exact hm.trans (Nat.mul_le_mul_right n.size (by omega))
  · exact hq.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right n.size (by omega)))
  · exact ht
  · exact BinaryGeometryWidth.geometryWidth_le_common n L m q cL cm cq hL hm hq

#print axioms prepareGlobal_geometry_price

#print axioms prepareGlobal_price

#print axioms globalAllowance_native
#print axioms preparationFactor_polylog

#print axioms prepareGlobalShape_price

#print axioms highAllowance_native
#print axioms highFactor_polylog

#print axioms bandAllowance_native
#print axioms bandFactor_polylog
#print axioms prepareTile_price

#print axioms prepareLeftBand_price
#print axioms prepareRightBand_price
#print axioms prepareHigh_price

end
end ThinMatrix.BinaryBackendCosts


namespace ThinMatrix.BinaryPreparationComputed
open AdaptiveBitBounds GlobalAddressBitBounds
open scoped BigOperators
noncomputable section

def sizeLogConstant : ℝ := 2+1/Real.log 2

theorem sizeLogConstant_pos : 0 < sizeLogConstant := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold sizeLogConstant
  positivity

theorem size_add_one_le_log (n : ℕ) (hn : 3 ≤ n) :
    ((n.size+1:ℕ):ℝ) ≤ sizeLogConstant*Real.log (n:ℝ) :=
  BackendCostRefinement.size_add_one_le_log n hn

def preparationLogConstant (C : ℕ) : ℝ := (C:ℝ)*sizeLogConstant^12

theorem preparationLogConstant_nonneg (C : ℕ) : 0 ≤ preparationLogConstant C := by
  unfold preparationLogConstant
  positivity

/-- Converts the actual natural-number polynomial factor without changing
its degree or assuming a cost bound for any backend operation. -/
theorem naturalFactor_le_logFactor (C n : ℕ) (hn : 3 ≤ n) :
    ((C*(n.size+1)^12:ℕ):ℝ) ≤ preparationLogConstant C*(Real.log (n:ℝ))^12 := by
  have hs := size_add_one_le_log n hn
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (n.size+1)) hs 12
  calc
    _ = (C:ℝ)*(((n.size+1:ℕ):ℝ)^12) := by push_cast; rfl
    _ ≤ (C:ℝ)*(sizeLogConstant*Real.log (n:ℝ))^12 :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg C)
    _ = _ := by unfold preparationLogConstant; rw [mul_pow]; ring

theorem naturalFactor_mul_le_logFactor (C n : ℕ) (X : ℝ)
    (hn : 3 ≤ n) (hX : 0 ≤ X) :
    ((C*(n.size+1)^12:ℕ):ℝ)*X ≤
      preparationLogConstant C*(Real.log (n:ℝ))^12*X :=
  mul_le_mul_of_nonneg_right (naturalFactor_le_logFactor C n hn) hX

theorem log2_le_exponent {N e : ℕ} (hN : N ≤ 2^e) : N.log2 ≤ e := by
  by_cases hzero : N = 0
  · simp [hzero]
  have hpow : (2:ℕ)^e < 2^(e+1) := by
    rw [pow_succ]
    have hp : 0 < (2:ℕ)^e := by positivity
    omega
  exact Nat.le_of_lt_succ ((Nat.log2_lt hzero).mpr (hN.trans_lt hpow))

/-- The four constants come from the actual computed phase geometry.
The logarithmic outer dimension is derived from its full polynomial cap. -/
theorem computed_geometry_caps (n : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := Nat.ceil (RealCertificate.c*(m:ℝ))
    let q := call.cyclic AlignedCertificate.S
    let N := PhaseGeometry.outerSize call AlignedCertificate.S n
    L ≤ computedLengthConstant*n.size ∧
    m ≤ computedIndexConstant*n.size ∧
    q ≤ 2^(computedCyclicConstant*n.size) ∧
    N.log2 ≤ computedOuterConstant*n.size := by
  exact ⟨computed_roundedLength_le_size n hn call,
    computed_innerPower_le_size n hn call,
    computed_cyclic_le_pow_size n hn call,
    log2_le_exponent (computed_outer_le_pow_size n hn call)⟩

theorem phaseRawSum_nonneg (n : ℕ)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    0 ≤ ComputedReductionCosts.phaseRawSum n call := by
  unfold ComputedReductionCosts.phaseRawSum
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (ReductionCosts.rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i)

/-- A preparation collector may supply its proved natural-factor bound;
this lemma converts that bound uniformly for all computed calls. -/
theorem eventual_preparation_factor (C : ℕ)
    (work : (n : ℕ) → ComputedPhaseGeometry.Call AlignedCertificate.R n → ℝ)
    (hwork : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      work n call ≤ ((C*(n.size+1)^12:ℕ):ℝ)*ComputedReductionCosts.phaseRawSum n call) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      work n call ≤ preparationLogConstant C*(Real.log (n:ℝ))^12*
        ComputedReductionCosts.phaseRawSum n call := by
  filter_upwards [hwork,Filter.eventually_ge_atTop (3:ℕ)] with n hw hn
  intro call
  exact (hw call).trans
    (naturalFactor_mul_le_logFactor C n _ hn (phaseRawSum_nonneg n call))

/-- Existential-constant form for direct use in eventual asymptotic bounds. -/
theorem exists_eventual_preparation_factor (C : ℕ)
    (work : (n : ℕ) → ComputedPhaseGeometry.Call AlignedCertificate.R n → ℝ)
    (hwork : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      work n call ≤ ((C*(n.size+1)^12:ℕ):ℝ)*ComputedReductionCosts.phaseRawSum n call) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      work n call ≤ C'*(Real.log (n:ℝ))^12*ComputedReductionCosts.phaseRawSum n call :=
  ⟨preparationLogConstant C,preparationLogConstant_nonneg C,eventual_preparation_factor C work hwork⟩

#print axioms naturalFactor_le_logFactor
#print axioms computed_geometry_caps
#print axioms eventual_preparation_factor
#print axioms exists_eventual_preparation_factor
end
end ThinMatrix.BinaryPreparationComputed


namespace ThinMatrix.BinaryResourcePhase
noncomputable section
open ThinMatrixBackend ThinProductCosts BackendCostRefinement BackendNumeratorBounds
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- Closed finite budget comparison. The statement contains no executable
multiplier, input arrays, request list, or pipeline domination premise. -/
theorem resourceBudget_le_rounded (N Q L m t q μ B : ℕ)
    (hm : m ≤ L) (hq : 1 ≤ q) (hm0 : 0 < m)
    (hL : L = Nat.ceil (RealCertificate.c*(m:ℝ)))
    (htheta : t = Nat.ceil (2*RealCertificate.theta*(m:ℝ)))
    (hgeometry : gridSide L m ≤ N)
    (hband : (bandSourceBudget L m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape L m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) :
    ((globalPreparationBudget N L m t q μ +
      Q*globalQueryRefinement N L m B*
        (ThinProductCosts.lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) : ℕ) : ℝ) ≤
      BackendCostRefinement.roundedCostBound N Q m q μ B 1 := by
  subst L
  subst t
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let t := Nat.ceil (2*RealCertificate.theta*(m:ℝ))
  have hf : ((globalPreparationBudget N L m t q μ +
      Q*globalQueryRefinement N L m B*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) : ℕ) : ℝ) ≤
      256*(commonFactor N L m B:ℝ)*
        (uniformCost N Q L m t q (2*m+1) 1 μ 1:ℝ)+
      (((prepareShape L m).operations:ℝ)+
        20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m+
        2*(TilingCosts.bandCount N (tileWidth L m):ℝ)*bandSourceBudget L m q) := by
    have hn : globalPreparationBudget N L m t q μ +
        Q*globalQueryRefinement N L m B*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) ≤
        256*commonFactor N L m B*uniformCost N Q L m t q (2*m+1) 1 μ 1+
          ((prepareShape L m).operations+
            20*q*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*4^m+
            2*TilingCosts.bandCount N (tileWidth L m)*bandSourceBudget L m q) := by
      simpa only [Nat.add_assoc] using global_finite_comparison N Q L m t q μ B hm hq
    exact_mod_cast hn
  have hp := rounded_uniform_power RealCertificate.c RealCertificate.theta N Q m q (2*m+1)
    1 μ 1 (by norm_num [RealCertificate.c]) (by norm_num [RealCertificate.theta])
    (by norm_num [RealCertificate.theta]) hm0 hgeometry
  have hs := source_extras_bound N m q hm0 hgeometry hband hshape
  have hc : 20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m ≤
      40*(q:ℝ)*N*(4:ℝ)^m := by
    exact_mod_cast inputCopies_bound N L m q hm hgeometry
  have he : ((prepareShape L m).operations:ℝ)+
      20*(q:ℝ)*TilingCosts.bandCount N (tileWidth L m)*tileWidth L m*(4:ℝ)^m+
      2*(TilingCosts.bandCount N (tileWidth L m):ℝ)*bandSourceBudget L m q ≤
      40*(q:ℝ)*N*(4:ℝ)^m+
      64*(q:ℝ)*N*((L:ℝ)+1)*((4:ℝ)^m)^RealCertificate.Ebox+
      (q:ℝ)*(N:ℝ)^2*((L:ℝ)+1)^2*((4:ℝ)^m)^(-RealCertificate.G) := by
    dsimp only at hs
    linarith
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 256*(commonFactor N L m B:ℝ) by positivity)
  simpa only [roundedCostBound, Nat.mul_one, Nat.cast_one, mul_one] using
    hf.trans (add_le_add hp' he)

#print axioms resourceBudget_le_rounded



/-- Explicit global preparation and request-resource allowance. This bound
contains no backend execution or actual-pipeline hypothesis. -/
theorem resourceBudget_le_raw (N n L m t q μ B : ℕ)
    (hm : m ≤ L) (hq : 1 ≤ q) (hm0 : 0 < m)
    (hL : L=Nat.ceil (RealCertificate.c*(m:ℝ)))
    (htheta : t=Nat.ceil (2*RealCertificate.theta*(m:ℝ)))
    (hgeometry : gridSide L m ≤ N)
    (hband : (bandSourceBudget L m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (hshape : ((prepareShape L m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G))
    (allowance : ℝ) (hallowance : 1 ≤ allowance)
    (hμ : (μ:ℝ) ≤ (q:ℝ)*allowance) :
    ((globalPreparationBudget N L m t q μ +
      (3*n^2)*globalQueryRefinement N L m B*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)):ℕ) ≤
      3*allowance*backendLocalFactor N L m B*
        ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i := by
  have hf := resourceBudget_le_rounded N (3*n^2) L m t q μ B
    hm hq hm0 hL htheta hgeometry hband hshape
  have hw := roundedCostBound_query_mul_bound N (n^2) m q μ B 1 3 (by decide)
  have hr := roundedCostBound_le_raw n N m q μ B 1 allowance
    (by linarith) (by simpa only [Nat.cast_one] using hallowance)
    (by simpa only [Nat.mul_one] using hμ)
  rw [←hL] at hr
  calc
    _ ≤ roundedCostBound N (3*n^2) m q μ B 1 := hf
    _ ≤ (3:ℝ)*roundedCostBound N (n^2) m q μ B 1 := hw
    _ ≤ 3*(allowance*backendLocalFactor N L m B*
        ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

def resourceCoefficient : ℝ :=
  3*AlignedAPSPCosts.binaryAllowanceConstant*
    backendCoefficientConstant AlignedCertificate.R
      (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)

def resourceLogDegree : ℕ := 24

/-- Closed phase allowance for the computed geometry. All resource widths,
full-vector multiplier work and full-grid fit are discharged uniformly. -/
theorem eventual_resourceBudget_le_phase :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
      let L := ComputableParameters.ordinaryLength m
      let t := ComputableParameters.channelLength m
      let q := call.cyclic AlignedCertificate.S
      let N := PhaseGeometry.outerSize call AlignedCertificate.S n
      let μ := BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)
      let B := numeratorBitBudget L m q 1
      ((globalPreparationBudget N L m t q μ +
        (3*n^2)*globalQueryRefinement N L m B*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)):ℕ) ≤
        resourceCoefficient*(Real.log (n:ℝ))^resourceLogDegree*
          ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta n N ((4:ℝ)^m) q i := by
  filter_upwards [computed_source_budgets_fit AlignedCertificate.R AlignedCertificate.S,
    ComputedPhaseGeometry.actual_innerPower_uniformly_large AlignedCertificate.R 1,
    ComputedPhaseGeometry.all_computed_candidate_tiles_fit,
    Filter.eventually_ge_atTop (3:ℕ)] with n hsource hlarge hgrid hn
  intro call
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let μ := BinaryMultiplierAdapter.workBound q (AdaptiveBitBounds.highInputBudget L m 1)
  let B := numeratorBitBudget L m q 1
  let CB := backendCoefficientConstant AlignedCertificate.R
    (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)
  let ell := Real.log (n:ℝ)
  let A := AlignedAPSPCosts.binaryAllowance n
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  have hL : L=Nat.ceil (RealCertificate.c*(m:ℝ)) := ComputableParameters.ordinaryLength_eq m
  have htheta : t=Nat.ceil (2*RealCertificate.theta*(m:ℝ)) := ComputableParameters.channelLength_eq m
  have hm : m ≤ L := ComputableParameters.ordinaryLength_lower m
  have hq : 1 ≤ q := by
    change 0 < (call.factors.drop AlignedCertificate.S).prod
    exact List.prod_pos (fun p hp =>
      (PrimePool.candidate_prime (call.valid p (List.mem_of_mem_drop hp))).pos)
  have hm0 : 0 < m := by
    have hm := hlarge call AlignedCertificate.S
    omega
  have hgeometry : gridSide L m ≤ N := by
    simpa only [gridSide] using hgrid call
  have hbudgets := hsource call q hq
  change (bandSourceBudget (Nat.ceil (RealCertificate.c*(m:ℝ))) m q:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) ∧
    ((prepareShape (Nat.ceil (RealCertificate.c*(m:ℝ))) m).operations:ℝ) ≤
      (q:ℝ)*((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G) at hbudgets
  rw [←hL] at hbudgets
  have hA : 1 ≤ A := AlignedAPSPCosts.binaryAllowance_ge_one n hn
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hμ : (μ:ℝ) ≤ (q:ℝ)*A := by
    dsimp only [μ]
    rw [hL]
    exact AlignedAPSPCosts.computed_binary_work_le_allowance n hn call
  have hbits : (B:ℝ) ≤ AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R*ell := by
    dsimp only [B]
    rw [hL]
    exact AlignedAPSPCosts.Numerator.computed_numeratorBits_log_bound
      AlignedCertificate.R AlignedCertificate.S n hn call
  have hfactor : backendLocalFactor N L m B ≤ CB*ell^13 := by
    rw [hL]
    exact computed_backendLocalFactor_le_polylog
      AlignedCertificate.R AlignedCertificate.S n B hn call
      (AlignedAPSPCosts.Numerator.numeratorBitsConstant AlignedCertificate.R)
      (AlignedAPSPCosts.Numerator.numeratorBitsConstant_nonneg AlignedCertificate.R) hbits
  have hraw : 0 ≤ rawSum := by
    apply Finset.sum_nonneg
    intro i _
    exact ReductionCosts.rawTerm_nonneg _ _ _ _ _ _ (Nat.cast_nonneg n)
      (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) i
  have hf := resourceBudget_le_raw N n L m t q μ B hm hq hm0 hL htheta hgeometry
    hbudgets.1 hbudgets.2 A hA hμ
  calc
    _ ≤ 3*A*backendLocalFactor N L m B*rawSum := hf
    _ ≤ 3*A*(CB*ell^13)*rawSum :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor (by positivity)) hraw
    _ = _ := by
      dsimp only [A,AlignedAPSPCosts.binaryAllowance,resourceCoefficient,resourceLogDegree,CB,ell,rawSum]
      rw [show (24:ℕ)=11+13 by decide,pow_add]
      ring

#print axioms resourceBudget_le_raw
#print axioms eventual_resourceBudget_le_phase

end
end ThinMatrix.BinaryResourcePhase

namespace ThinMatrix.BinaryBackendCosts
open AdaptiveBitBounds
open scoped BigOperators
noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Fixed constants for the actual computed phase. The input coefficient
cap is one, so the LOW width uses degree zero. -/
def computedPreparationConstant : ℕ :=
  preparationConstant 0 (9*computedLengthConstant+9)
    (9*computedIndexConstant+9) (9*computedCyclicConstant+9)

attribute [local irreducible] computedIndexConstant computedLengthConstant
  computedCyclicConstant computedPreparationConstant AlignedCertificate.R AlignedCertificate.S

/-- The actual computed public parameters supply all preparation widths. -/
theorem computed_prepareGlobal_price (n D : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := ComputableParameters.ordinaryLength m
    let t := ComputableParameters.channelLength m
    let q := call.cyclic AlignedCertificate.S
    let N := PhaseGeometry.outerSize call AlignedCertificate.S n
    ∀ (left : BinaryBackendExecution.OriginalLeft N D q)
      (right : BinaryBackendExecution.OriginalRight N D q),
    (∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1) →
    (∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1) →
    (BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right).bitSteps ≤
      computedPreparationConstant*(n.size+1)^12*
        BackendCostRefinement.globalPreparationBudget N L m t q (fullBudget L m q) := by
  dsimp only
  intro left right hl hr
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  have hqpos : 0 < q := by
    change 0 < (call.factors.drop AlignedCertificate.S).prod
    exact List.prod_pos (fun p hp =>
      (PrimePool.candidate_prime (call.valid p (List.mem_of_mem_drop hp))).pos)
  letI : NeZero q := ⟨by omega⟩
  have hL : L ≤ computedLengthConstant*n.size := by
    dsimp only [L]
    rw [ComputableParameters.ordinaryLength_eq]
    exact computed_roundedLength_le_size n hn call
  have hm : m ≤ computedIndexConstant*n.size := computed_innerPower_le_size n hn call
  have hq : q ≤ 2^(computedCyclicConstant*n.size) := computed_cyclic_le_pow_size n hn call
  have ht : t ≤ 2*m := by
    dsimp only [t]
    rw [ComputableParameters.channelLength_eq]
    exact rounded_cutoff_le m
  have hc := prepareGlobal_geometry_price left right hl hr n
    computedLengthConstant computedIndexConstant computedCyclicConstant (by omega)
    (ComputableParameters.ordinaryLength_lower m) hL hm hq ht
  simpa only [computedPreparationConstant] using hc

def preparationPhaseConstant : ℝ :=
  BinaryPreparationComputed.preparationLogConstant computedPreparationConstant*
    BinaryResourcePhase.resourceCoefficient

/-- The preparation part of the retained binary execution is bounded by
the six raw phase terms. No multiplier, scalar width, or preparation-time
assumption occurs in the statement. -/
theorem eventual_prepareGlobal_le_phase :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
      let L := ComputableParameters.ordinaryLength m
      let t := ComputableParameters.channelLength m
      let q := call.cyclic AlignedCertificate.S
      let N := PhaseGeometry.outerSize call AlignedCertificate.S n
      ∀ D (left : BinaryBackendExecution.OriginalLeft N D q)
        (right : BinaryBackendExecution.OriginalRight N D q),
      (∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1) →
      (∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1) →
      ((BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
        (BinaryGeometryWidth.geometryWidth L m q) 1 left right).bitSteps:ℝ) ≤
        preparationPhaseConstant*(Real.log (n:ℝ))^36*
          ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
            n N ((4:ℝ)^m) q i := by
  filter_upwards [BinaryResourcePhase.eventual_resourceBudget_le_phase,
    Filter.eventually_ge_atTop (3:ℕ)] with n hresource hn
  intro call
  dsimp only
  intro D left right hl hr
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let P := BackendCostRefinement.globalPreparationBudget N L m t q (fullBudget L m q)
  let G := BinaryPreparationComputed.preparationLogConstant computedPreparationConstant
  let ell := Real.log (n:ℝ)
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  have hprep := computed_prepareGlobal_price n D hn call left right hl hr
  have hprepR : ((BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right).bitSteps:ℝ) ≤
      ((computedPreparationConstant*(n.size+1)^12:ℕ):ℝ)*(P:ℝ) := by
    exact_mod_cast hprep
  have hlog := BinaryPreparationComputed.naturalFactor_mul_le_logFactor
    computedPreparationConstant n (P:ℝ) hn (Nat.cast_nonneg P)
  have hP : (P:ℝ) ≤ BinaryResourcePhase.resourceCoefficient*ell^24*rawSum := by
    apply (show (P:ℝ) ≤ ((P+(3*n^2)*BackendCostRefinement.globalQueryRefinement N L m
        (BackendNumeratorBounds.numeratorBitBudget L m q 1)*
        (ThinProductCosts.lowCoefficientCost m t q (2*m+1)+
          ThinProductCosts.highCoefficientReads m t):ℕ):ℝ) by exact_mod_cast Nat.le_add_right P _).trans
    exact hresource call
  have hG : 0 ≤ G*ell^12 := by
    exact mul_nonneg (BinaryPreparationComputed.preparationLogConstant_nonneg _)
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _)
  calc
    _ ≤ G*ell^12*(P:ℝ) := hprepR.trans hlog
    _ ≤ G*ell^12*(BinaryResourcePhase.resourceCoefficient*ell^24*rawSum) :=
      mul_le_mul_of_nonneg_left hP hG
    _ = _ := by
      dsimp only [preparationPhaseConstant,G,ell,rawSum]
      rw [show (36:ℕ)=12+24 by decide,pow_add]
      ring

#print axioms computed_prepareGlobal_price
#print axioms eventual_prepareGlobal_le_phase
end
end ThinMatrix.BinaryBackendCosts



/-!
Single-process compilation succeeded after the parent's compiler slot freed.
The cache bound covers every arbitrary physical key, including missing-key
zero defaults. No correctness/native oracle is replayed.
-/
namespace ThinMatrix.BinaryLowCacheBound
noncomputable section
open CacheBounds SharedEncoder SparseLocalForms

def DenseBlockBound {q width : ℕ} (A : ℕ) (block : DenseVector q width) : Prop :=
  ∀ d r, |denseRead block d r| ≤ (A:ℤ)

/-- Every returned leaf is the scalar read of a terminal formed array.
This induction supplies the missing link from all-formed bounds to leaves. -/
theorem dense_run_leaves_property (L m t q width : ℕ) (side : Bool)
    (P : CacheDenseLowering.Block q width → Prop)
    (n : ℕ) (dims : Fin n → ℕ) (depth : ℕ)
    (parents : List (CacheDenseLowering.DataNode q width (2*L) n dims))
    (hformed : ∀ s ∈ (CacheDenseLowering.run L m t q width side n dims depth parents).formed,
      ∀ a, P (SharedEncoder.read s.remaining s.dims s.node.data a)) :
    ∀ leaf ∈ (CacheDenseLowering.run L m t q width side n dims depth parents).leaves,
      P leaf.2 := by
  induction n generalizing depth with
  | zero =>
      intro leaf hleaf
      simp only [CacheDenseLowering.run] at hleaf hformed
      obtain ⟨parent, hparent, rfl⟩ := List.mem_map.mp hleaf
      have hmem : (⟨depth, 0, dims, parent⟩ : SharedEncoder.Stored
          (CacheDenseLowering.Block q width) (2*L)) ∈
          parents.map (fun node => ⟨depth, 0, dims, node⟩) :=
        List.mem_map.mpr ⟨parent, hparent, rfl⟩
      simpa only [SharedEncoder.read] using
        hformed ⟨depth, 0, dims, parent⟩ hmem (fun i => Fin.elim0 i)
  | succ n ih =>
      intro leaf hleaf
      by_cases hd : depth < 2*L
      · simp only [CacheDenseLowering.run, dif_pos hd] at hleaf hformed
        apply ih _ _ _ ?_ leaf hleaf
        intro s hs a
        exact hformed s (List.mem_append_right _ hs) a
      · simp only [CacheDenseLowering.run, dif_neg hd, List.not_mem_nil] at hleaf

theorem dense_encode_leaves_property (L m t q width : ℕ) (side : Bool)
    (input : CacheDenseLowering.Data q width (2*L) (SharedEncoder.rootDims L side))
    (P : CacheDenseLowering.Block q width → Prop)
    (hformed : ∀ s ∈ (CacheDenseLowering.encode L m t q width side input).formed,
      ∀ a, P (SharedEncoder.read s.remaining s.dims s.node.data a)) :
    ∀ leaf ∈ (CacheDenseLowering.encode L m t q width side input).leaves, P leaf.2 :=
  dense_run_leaves_property L m t q width side P (2*L) (SharedEncoder.rootDims L side)
    0 [⟨CappedEnumeration.zeroWord (2*L), input⟩] hformed

/-- Trie payload invariant. Repeated stored keys remain harmless since
every possible replacement has the same bound. -/
def TrieBound {α : Type*} (P : α → Prop) (table : StoredHighDP.Trie α) : Prop :=
  ∀ key value, table.read key = some value → P value

theorem trie_empty_bound {α : Type*} (P : α → Prop) :
    TrieBound P (StoredHighDP.Trie.empty : StoredHighDP.Trie α) := by
  intro key value hread
  rw [BinaryLowEncoder.TrieProjection.read_empty] at hread
  contradiction

theorem trie_write_bound {α : Type*} (P : α → Prop) (table : StoredHighDP.Trie α)
    (key : List Label) (value : α) (htable : TrieBound P table) (hvalue : P value) :
    TrieBound P (table.write key value) := by
  intro other found hread
  by_cases he : other = key
  · subst other
    rw [StoredHighDP.Trie.read_write_same] at hread
    cases hread
    exact hvalue
  · rw [StoredHighDP.Trie.read_write_other table key other value he] at hread
    exact htable other found hread

theorem storePairs_bound {α : Type*} {N : ℕ} (P : α → Prop)
    (rows : List (Word N × α)) (table : StoredHighDP.Trie α)
    (htable : TrieBound P table) (hrows : ∀ row ∈ rows, P row.2) :
    TrieBound P (CachedLowQuery.storePairs rows table).1 := by
  induction rows generalizing table with
  | nil => exact htable
  | cons row rows ih =>
      simp only [CachedLowQuery.storePairs]
      apply ih
      · simpa only [StoredHighDP.Trie.writeCounted_value] using
          trie_write_bound P table (StoredHighDP.key row.1) row.2 htable (hrows row (by simp))
      · intro leaf hleaf
        exact hrows leaf (List.mem_cons_of_mem row hleaf)

/-- Arbitrary cache keys either find a bounded stored leaf or the literal
zero block. No Retained premise and no key-uniqueness premise is needed. -/
theorem native_read_storePairs_bound {N q width : ℕ}
    (rows : List (Word N × DenseVector q width)) (A : ℕ)
    (hrows : ∀ row ∈ rows, DenseBlockBound A row.2)
    (key : ArrayKeys.Key N) (d : Fin width) (r : Fin q) :
    |denseRead ((CachedLowQuery.readKeyBlockCounted
      (CachedLowQuery.storePairs rows .empty).1 key).1) d r| ≤ (A:ℤ) := by
  let table := (CachedLowQuery.storePairs rows .empty).1
  have ht : TrieBound (DenseBlockBound A) table :=
    storePairs_bound (DenseBlockBound A) rows .empty (trie_empty_bound _) hrows
  change |denseRead ((ArrayKeys.read table key).1.getD (CachedLowQuery.zeroBlock q width)) d r| ≤ _
  rw [ArrayKeys.read_value]
  cases hread : table.read (StoredHighDP.key (ArrayKeys.toWord key)) with
  | none => simp [CachedLowQuery.zeroBlock, SparseLocalForms.denseRead]
  | some block =>
      simp only [Option.getD_some]
      exact ht _ block hread d r

/-- Native source preparation inherits the all-formed budget, then stores
its returned leaves. This supplies the lookup invariant used by binary LOW. -/
theorem native_prepareSource_read_bound {L m t q A width : ℕ} [NeZero q]
    (hA : 1 ≤ A) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoefficientBounds.CoeffBound (X a) (2^(L+m)*A))
    (key : ArrayKeys.Key (2*L)) (d : Fin width) (r : Fin q) :
    |denseRead ((CachedLowQuery.readKeyBlockCounted
      (CacheDenseLowering.prepareSource (m:=m) (t:=t) (width:=width) side X).1 key).1) d r| ≤
      (CoefficientBounds.uniformBudget L m t q A:ℤ) := by
  let input := CacheDenseLowering.constantInput (width:=width) (2*L)
    (SharedEncoder.rootDims L side) (CacheDenseLowering.sourceVectorInput side X)
  have hformed : ∀ s ∈ (CacheDenseLowering.encode L m t q width side input).formed,
      ∀ a, DenseBlockBound (CoefficientBounds.uniformBudget L m t q A)
        (SharedEncoder.read s.remaining s.dims s.node.data a) := by
    intro s hs a
    exact CacheSchemaBitBounds.source_formed_bound hA width side X hX s hs a
  have hleaves := dense_encode_leaves_property L m t q width side input
    (DenseBlockBound (CoefficientBounds.uniformBudget L m t q A)) hformed
  change |denseRead ((CachedLowQuery.readKeyBlockCounted
    (CachedLowQuery.storePairs (CacheDenseLowering.encode L m t q width side input).leaves .empty).1
      key).1) d r| ≤ _
  exact native_read_storePairs_bound _ _ hleaves key d r

/-- Actual binary cache lookup bound, transported through the already
proved scalar equality for its exact produced trie. W is unrestricted. -/
theorem prepareRawSource_cacheBound {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (hA : 1 ≤ A) (side : Bool) (raw : BinarySourceFormation.RawStore L q)
    (hsource : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) (2^(L+m)*A)) :
    BinaryLowQuery.CacheBound
      (BinaryLowEncoder.prepareRawSource (m:=m) (t:=t) W side raw).table
      (CoefficientBounds.uniformBudget L m t q A) := by
  intro key d r
  rw [BinaryLowEncoder.prepareRawSource_cacheRefines (m:=m) (t:=t) W side raw key]
  exact native_prepareSource_read_bound hA side _ hsource key d r

theorem prepareLeftBand_cacheBound {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (hA : 1 ≤ A) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (run : Fin (2*m+1)) :
    BinaryLowQuery.CacheBound
      (((BinaryBackendExecution.prepareLeftBand (t:=t) W shape left).low.get run).table)
      (CoefficientBounds.uniformBudget L m t q A) := by
  have hs := BinaryBandBounds.left_source_coeffBound shape left hl run
  have hc := prepareRawSource_cacheBound (m:=m) (t:=t) W hA true
    ((BinaryBandSource.prepareLeft shape left).runs.get run) hs
  simpa only [BinaryBackendExecution.prepareLeftBand, Vector.get_map] using hc

theorem prepareRightBand_cacheBound {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (hA : 1 ≤ A) (shape : ThinMatrixBackend.ShapePlan L m)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (run : Fin (2*m+1)) :
    BinaryLowQuery.CacheBound
      (((BinaryBackendExecution.prepareRightBand (t:=t) W shape right).low.get run).table)
      (CoefficientBounds.uniformBudget L m t q A) := by
  have hs := BinaryBandBounds.right_source_coeffBound shape right hr run
  have hc := prepareRawSource_cacheBound (m:=m) (t:=t) W hA false
    ((BinaryBandSource.prepareRight shape right).runs.get run) hs
  simpa only [BinaryBackendExecution.prepareRightBand, Vector.get_map] using hc

theorem bandRunCaches_bound {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (hA : 1 ≤ A) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A) :
    BinaryLowQuery.RunBound (BinaryBackendExecution.bandRunCaches
      (BinaryBackendExecution.prepareLeftBand (t:=t) W shape left)
      (BinaryBackendExecution.prepareRightBand (t:=t) W shape right))
      (CoefficientBounds.uniformBudget L m t q A) := by
  intro run
  constructor
  · simpa only [BinaryBackendExecution.bandRunCaches, Vector.get_ofFn] using
      prepareLeftBand_cacheBound (t:=t) W hA shape left hl run
  · simpa only [BinaryBackendExecution.bandRunCaches, Vector.get_ofFn] using
      prepareRightBand_cacheBound (t:=t) W hA shape right hr run

/-- Cap-one instance requested by the actual indicator-source producer. -/
theorem bandRunCaches_bound_one {L m t q : ℕ} [NeZero q]
    (W : ℕ) (shape : ThinMatrixBackend.ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1) :
    BinaryLowQuery.RunBound (BinaryBackendExecution.bandRunCaches
      (BinaryBackendExecution.prepareLeftBand (t:=t) W shape left)
      (BinaryBackendExecution.prepareRightBand (t:=t) W shape right))
      (CoefficientBounds.uniformBudget L m t q 1) :=
  bandRunCaches_bound W (by decide) shape left right hl hr

end
end ThinMatrix.BinaryLowCacheBound

#print axioms ThinMatrix.BinaryLowCacheBound.dense_run_leaves_property
#print axioms ThinMatrix.BinaryLowCacheBound.native_prepareSource_read_bound
#print axioms ThinMatrix.BinaryLowCacheBound.prepareRawSource_cacheBound
#print axioms ThinMatrix.BinaryLowCacheBound.bandRunCaches_bound_one

namespace ThinMatrix.BinaryQueryCosts
open scoped BigOperators
open ThinMatrixBackend BinaryBackendExecution
open BackendCostRefinement ThinProductCosts
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- K is the nonempty key count, C bounds one complete row value, and U is
the per-key price. This is exactly the requested HIGH integration factor. -/
theorem sumQueryRows_bound {runs : ℕ}
    (rows : Vector (ToomCook.Counted BinaryCell.Cell) runs) (K C U : ℕ)
    (hK : 1 ≤ K)
    (hvalue : ∀ i, (rows.get i).value.view.natAbs ≤ C)
    (hwork : ∀ i, (rows.get i).operations ≤ K*U) :
    (sumQueryRows rows).value.view.natAbs ≤ runs*C ∧
    (sumQueryRows rows).operations ≤
      (runs*(U+BackendScalarBits.backendScalarUnit (runs*C).size+10)+1)*K := by
  have hrows : rows.toList = List.ofFn (fun i => rows.get i) := by
    rw [← Vector.toList_ofFn]
    apply congrArg Vector.toList
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rfl
  let cells := rows.toList.map (fun row => row.value)
  have hlen : cells.length = runs := by simp [cells]
  have hcells : ∀ x ∈ cells, x.view.natAbs ≤ C := by
    intro x hx
    have hx' : x ∈ List.ofFn (fun i => (rows.get i).value) := by
      simpa only [cells, hrows, List.map_ofFn, Function.comp_def] using hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
    exact hvalue i
  have hsumValue := BinaryHighTable.sumCells_bound C cells hcells
  have hsumWork := BinaryHighTable.sumCells_price_width C runs (runs*C).size cells
    (by omega) le_rfl hcells
  have hrowsWork : (rows.toList.map (fun row => row.operations)).sum ≤ runs*(K*U) := by
    rw [hrows, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin runs, K*U := Finset.sum_le_sum (fun i _ => hwork i)
      _ = _ := by simp
  constructor
  · simpa only [sumQueryRows, cells, hlen] using hsumValue
  · change (rows.toList.map (fun row => row.operations)).sum+
      (BinaryHighTable.sumCells cells).operations+8*runs ≤ _
    have hsumWork' : (BinaryHighTable.sumCells cells).operations ≤
        runs*(BackendScalarBits.backendScalarUnit (runs*C).size+2)+1 := by
      simpa only [hlen] using hsumWork
    have hscale : runs*(BackendScalarBits.backendScalarUnit (runs*C).size+10)+1 ≤
        (runs*(BackendScalarBits.backendScalarUnit (runs*C).size+10)+1)*K :=
      Nat.le_mul_of_pos_right _ hK
    calc
      _ ≤ runs*(K*U)+(runs*(BackendScalarBits.backendScalarUnit (runs*C).size+2)+1)+8*runs :=
        Nat.add_le_add_right (Nat.add_le_add hrowsWork hsumWork') _
      _ = runs*(K*U)+(runs*(BackendScalarBits.backendScalarUnit (runs*C).size+10)+1) := by ring
      _ ≤ runs*(K*U)+(runs*(BackendScalarBits.backendScalarUnit (runs*C).size+10)+1)*K :=
        Nat.add_le_add_left hscale _
      _ = _ := by ring

/-- The original-cell cap alone supplies all actual stored HIGH caps. W is
only the LOW/cache width and does not enter the HIGH cap or HIGH price. -/
theorem actual_highRows_bound {L m t q A : ℕ} [NeZero q]
    (W : ℕ) (shape : ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (ht : t ≤ 2*m) (d : QueryMetadata L m) (r : Fin q) :
    let reads := ThinProductCosts.highCoefficientReads m t
    let AHIGH := 5^(2*L+1)*(q*(AdaptiveBitBounds.highInputBudget L m A)^2)
    let rowCap := reads*AHIGH
    let H := (2*m+1)*rowCap
    let highFactor := (2*m+1)*(BinaryHighTable.queryUnit L (2*m) rowCap.size+
      BackendScalarBits.backendScalarUnit H.size+10)+1
    let tile := prepareTile (t:=t) A
      (prepareLeftBand (t:=t) W shape left) (prepareRightBand (t:=t) W shape right)
    let rows := Vector.ofFn (fun i : Fin (2*m+1) => BinaryHighTable.query t d.embedding
      (Vector.ofFn d.outside) (tile.runs.get i).high.value r)
    (sumQueryRows rows).value.view.natAbs ≤ H ∧
      (sumQueryRows rows).operations ≤ highFactor*reads := by
  let reads := ThinProductCosts.highCoefficientReads m t
  let AHIGH := 5^(2*L+1)*(q*(AdaptiveBitBounds.highInputBudget L m A)^2)
  let rowCap := reads*AHIGH
  let tile := prepareTile (t:=t) A
    (prepareLeftBand (t:=t) W shape left) (prepareRightBand (t:=t) W shape right)
  let rows := Vector.ofFn (fun i : Fin (2*m+1) => BinaryHighTable.query t d.embedding
    (Vector.ofFn d.outside) (tile.runs.get i).high.value r)
  have hreads : 1 ≤ reads := by
    simpa only [reads, ThinProductCosts.highCoefficientReads_eq] using
      Nat.mul_le_mul (Nat.choose_pos ht) (Nat.one_le_pow _ _ (by decide : 1 ≤ 4))
  have htable (i : Fin (2*m+1)) : BinaryHighTable.Bounds.TableBound AHIGH
      (tile.runs.get i).high.value := by
    simpa only [tile, BinaryBackendExecution.prepareTile, Vector.get_ofFn,
      BinaryBackendExecution.prepareLeftBand, BinaryBackendExecution.prepareRightBand,
      BinaryBandBounds.prepareHigh, AHIGH] using
      BinaryBandBounds.prepareHigh_bound (t:=t) shape left right hA hl hr i
  have hvalue (i : Fin (2*m+1)) : (rows.get i).value.view.natAbs ≤ rowCap := by
    simpa only [rows, Vector.get_ofFn, rowCap, reads,
      ThinProductCosts.highCoefficientReads_eq] using
      BinaryHighTable.query_bound t AHIGH d.embedding (Vector.ofFn d.outside)
        (tile.runs.get i).high.value r (htable i)
  have hwork (i : Fin (2*m+1)) : (rows.get i).operations ≤
      reads*BinaryHighTable.queryUnit L (2*m) rowCap.size := by
    simpa only [rows, Vector.get_ofFn, rowCap, reads,
      ThinProductCosts.highCoefficientReads_eq] using
      BinaryHighTable.query_work t AHIGH d.embedding (Vector.ofFn d.outside)
        (tile.runs.get i).high.value r ht (htable i)
  exact sumQueryRows_bound rows reads rowCap
    (BinaryHighTable.queryUnit L (2*m) rowCap.size) hreads hvalue hwork



def highTableCap (L m q A : ℕ) : ℕ :=
  5^(2*L+1)*(q*(AdaptiveBitBounds.highInputBudget L m A)^2)

def highSumCap (L m t q A : ℕ) : ℕ :=
  (2*m+1)*(highCoefficientReads m t*highTableCap L m q A)

def highFactor (L m t q A : ℕ) : ℕ :=
  (2*m+1)*(BinaryHighTable.queryUnit L (2*m)
    (highCoefficientReads m t*highTableCap L m q A).size+
    BackendScalarBits.backendScalarUnit (highSumCap L m t q A).size+10)+1

def queryFactor (L m t q A ALeaf : ℕ) : ℕ :=
  1000000*(BinaryLowQuery.completeWidth L m (2*m) t q ALeaf (highSumCap L m t q A)+1)^3*
    (highFactor L m t q A+2)+1

/-- Actual retained tile query, including its HIGH rows, same-run sum,
complete normalization, and both tile/global locator terms. The remaining
LOW hypothesis names only actual stored leaf magnitudes. -/
theorem queryTile_cost_of_cache_bound {L m t q A : ℕ} [NeZero q]
    (N B W ALeaf : ℕ) (shape : ShapePlan L m)
    (left : BinaryBackendExecution.StoredLeftMatrix L m q)
    (right : BinaryBackendExecution.StoredRightMatrix L m q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ A)
    (hm : m ≤ L) (ht : t ≤ 2*m)
    (hbound : BinaryLowQuery.RunBound
      (bandRunCaches (prepareLeftBand (t:=t) W shape left)
        (prepareRightBand (t:=t) W shape right)) ALeaf)
    (row col : ThinMatrixBackend.OuterIndex L m) (r : Fin q) :
    (queryTileExecution shape
      (prepareLeftBand (t:=t) W shape left) (prepareRightBand (t:=t) W shape right)
      (prepareTile (t:=t) A (prepareLeftBand (t:=t) W shape left)
        (prepareRightBand (t:=t) W shape right)) row col r).result.operations+
      1000*(L+m+N.log2+1)^5 ≤
        queryFactor L m t q A ALeaf*globalQueryRefinement N L m B*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  let binaryLeft := prepareLeftBand (t:=t) W shape left
  let binaryRight := prepareRightBand (t:=t) W shape right
  let tile := prepareTile (t:=t) A binaryLeft binaryRight
  let nativeLeft := ThinMatrixBackend.prepareLeftBand (t:=t) shape (BinaryOriginalReader.viewData left)
  let nativeRight := ThinMatrixBackend.prepareRightBand (t:=t) shape (BinaryOriginalReader.viewData right)
  let native := ThinMatrixBackend.bandRunCaches nativeLeft nativeRight
  let caches := bandRunCaches binaryLeft binaryRight
  let d := BinaryBackendExecution.queryGeometry shape.environment row col
  let rows := Vector.ofFn (fun i : Fin (2*m+1) => BinaryHighTable.query t d.embedding
    (Vector.ofFn d.outside) (tile.runs.get i).high.value r)
  let high := sumQueryRows rows
  let H := highSumCap L m t q A
  let HF := highFactor L m t q A
  let P := 1000000*(BinaryLowQuery.completeWidth L m (2*m) t q ALeaf H+1)^3
  let Z := globalQueryRefinement N L m B
  let low := lowCoefficientCost m t q (2*m+1)
  let reads := highCoefficientReads m t
  have hhigh := actual_highRows_bound W shape left right hA hl hr ht d r
  change high.value.view.natAbs ≤ H ∧ high.operations ≤ HF*reads at hhigh
  have hh : |high.value.view| ≤ (H:ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hhigh.1
  have hcache := bandRunCaches_refines binaryLeft binaryRight nativeLeft nativeRight
    (prepareLeftBand_refines W shape left) (prepareRightBand_refines W shape right)
  have hc := BinaryLowQuery.queryCell_cost_polynomial t ALeaf H
    (Vector.ofFn d.embedding) (Vector.ofFn d.outside) caches native hcache hbound r high hh
  have hlcost := queryLowRuns_le_old_budget (t:=t) (Vector.ofFn d.embedding)
    (Vector.ofFn d.outside) native r hm (by omega) (by omega) (by omega)
  have hcontrol : lowQueryControl L m ≤ Z := by
    unfold Z globalQueryRefinement queryRefinement
    omega
  have hZ : 1 ≤ Z := by
    have hz : 0 < Z := by
      unfold Z globalQueryRefinement queryRefinement normalizationBudget
      positivity
    omega
  have hlow : 1 ≤ low := lowCoefficientCost_pos m t q (2*m+1) (Nat.pos_of_neZero q) (by omega)
  have hnative : (CachedLowQuery.queryLowRuns t (Vector.ofFn d.embedding)
      (Vector.ofFn d.outside) native r).2 ≤ Z*low :=
    hlcost.trans (Nat.mul_le_mul_right low hcontrol)
  have hone : 1 ≤ Z*low := by nlinarith
  have hFZ : HF ≤ (HF+2)*Z :=
    (show HF ≤ HF+2 by omega).trans (Nat.le_mul_of_pos_right _ hZ)
  have hinner : (CachedLowQuery.queryLowRuns t (Vector.ofFn d.embedding)
      (Vector.ofFn d.outside) native r).2+high.operations+1 ≤
        (HF+2)*Z*(low+reads) := by
    calc
      _ ≤ Z*low+HF*reads+Z*low := Nat.add_le_add (Nat.add_le_add hnative hhigh.2) hone
      _ = 2*Z*low+HF*reads := by ring
      _ ≤ (HF+2)*Z*low+(HF+2)*Z*reads := Nat.add_le_add
        (Nat.mul_le_mul_right low (Nat.mul_le_mul_right Z (by omega : 2 ≤ HF+2)))
        (Nat.mul_le_mul_right reads hFZ)
      _ = _ := by ring
  have hcomplete : (BinaryLowQuery.queryCell t (Vector.ofFn d.embedding)
      (Vector.ofFn d.outside) caches r high).operations ≤ P*((HF+2)*Z*(low+reads)) :=
    hc.trans (Nat.mul_le_mul_left P hinner)
  have hmeta : 1000*(L+m+1)^5+1000*(L+m+N.log2+1)^5 ≤ Z := by
    unfold Z globalQueryRefinement queryRefinement
    omega
  have hpay : 1000*(L+m+1)^5+1000*(L+m+N.log2+1)^5 ≤ Z*(low+reads) :=
    hmeta.trans (Nat.le_mul_of_pos_right _ (by omega))
  change (BinaryLowQuery.queryCell t (Vector.ofFn d.embedding)
    (Vector.ofFn d.outside) caches r high).operations+1000*(L+m+1)^5+
      1000*(L+m+N.log2+1)^5 ≤ _
  calc
    _ ≤ P*((HF+2)*Z*(low+reads))+Z*(low+reads) := by omega
    _ = _ := by dsimp only [queryFactor,P,HF,H,Z,low,reads]; ring


/-- The actual global query inherits the tile bound at its stored locator.
The LOW magnitude premise refers to the same prepared global band caches. -/
theorem queryGlobal_cost_of_cache_bound {N D L m t q A : ℕ} [NeZero q]
    (B W ALeaf : ℕ) (shape : ShapePlan L m)
    (inputLeft : BinaryBackendExecution.OriginalLeft N D q)
    (inputRight : BinaryBackendExecution.OriginalRight N D q)
    (hA : 1 ≤ A)
    (hl : ∀ i r, (BinaryCell.view ((inputLeft.get i).get r)).natAbs ≤ A)
    (hr : ∀ i r, (BinaryCell.view ((inputRight.get i).get r)).natAbs ≤ A)
    (hm : m ≤ L) (ht : t ≤ 2*m)
    (hbound : ∀ b c,
      BinaryLowQuery.RunBound (bandRunCaches
        ((prepareGlobalShape (t:=t) shape W A inputLeft inputRight).left.get b)
        ((prepareGlobalShape (t:=t) shape W A inputLeft inputRight).right.get c)) ALeaf)
    (i j : Fin N) (r : Fin q) :
    (queryGlobalExecution (ThinMatrixBackend.tileWidth_pos L m hm)
      (prepareGlobalShape (t:=t) shape W A inputLeft inputRight) i j r).result.operations ≤
        queryFactor L m t q A ALeaf*globalQueryRefinement N L m B*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  let hB := ThinMatrixBackend.tileWidth_pos L m hm
  let prepared := prepareGlobalShape (t:=t) shape W A inputLeft inputRight
  let bi := ThinMatrixBackend.storedLocate shape hB i
  let bj := ThinMatrixBackend.storedLocate shape hB j
  let row := RowIndexing.rowUnrank shape.layout bi.2
  let col := RowIndexing.rowUnrank shape.layout bj.2
  have hleaf := hbound bi.1 bj.1
  rw [prepareGlobalShape_left,prepareGlobalShape_right] at hleaf
  have htile := queryTile_cost_of_cache_bound N B W ALeaf shape
    (makeLeftBandStored shape inputLeft bi.1.val).value
    (makeRightBandStored shape inputRight bj.1.val).value hA
    (BinaryBandCopyBounds.makeLeftBandStored_natAbs shape inputLeft bi.1.val hl)
    (BinaryBandCopyBounds.makeRightBandStored_natAbs shape inputRight bj.1.val hr)
    hm ht hleaf row col r
  change (queryTileExecution shape (prepared.left.get bi.1) (prepared.right.get bj.1)
    ((prepared.tiles.get bi.1).get bj.1) row col r).result.operations+
      1000*(L+m+N.log2+1)^5 ≤ _
  dsimp only [prepared]
  rw [prepareGlobalShape_left,prepareGlobalShape_right,prepareGlobalShape_tile]
  exact htile


/-- Closed actual global query price for original zero/one coefficient
arrays. LOW cache leaves and missing-key zeros are bounded from those inputs;
no query-time, cache-width, or final-numerator premise is assumed. -/
theorem queryGlobal_cost_original_one {N D L m t q : ℕ} [NeZero q]
    (B W : ℕ) (shape : ShapePlan L m)
    (inputLeft : BinaryBackendExecution.OriginalLeft N D q)
    (inputRight : BinaryBackendExecution.OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((inputLeft.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((inputRight.get i).get r)).natAbs ≤ 1)
    (hm : m ≤ L) (ht : t ≤ 2*m) (i j : Fin N) (r : Fin q) :
    (queryGlobalExecution (ThinMatrixBackend.tileWidth_pos L m hm)
      (prepareGlobalShape (t:=t) shape W 1 inputLeft inputRight) i j r).result.operations ≤
        queryFactor L m t q 1 (CoefficientBounds.uniformBudget L m t q 1)*
          globalQueryRefinement N L m B*
          (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  have hbound : ∀ b c, BinaryLowQuery.RunBound (bandRunCaches
      ((prepareGlobalShape (t:=t) shape W 1 inputLeft inputRight).left.get b)
      ((prepareGlobalShape (t:=t) shape W 1 inputLeft inputRight).right.get c))
      (CoefficientBounds.uniformBudget L m t q 1) := by
    intro b c
    rw [prepareGlobalShape_left,prepareGlobalShape_right]
    exact BinaryLowCacheBound.bandRunCaches_bound_one W shape
      (makeLeftBandStored shape inputLeft b.val).value
      (makeRightBandStored shape inputRight c.val).value
      (BinaryBandCopyBounds.makeLeftBandStored_natAbs shape inputLeft b.val hl)
      (BinaryBandCopyBounds.makeRightBandStored_natAbs shape inputRight c.val hr)
  exact queryGlobal_cost_of_cache_bound B W (CoefficientBounds.uniformBudget L m t q 1)
    shape inputLeft inputRight (by decide) hl hr hm ht hbound i j r

#print axioms sumQueryRows_bound
#print axioms actual_highRows_bound
#print axioms queryTile_cost_of_cache_bound
#print axioms queryGlobal_cost_of_cache_bound
#print axioms queryGlobal_cost_original_one

end
end ThinMatrix.BinaryQueryCosts



namespace ThinMatrix.BinaryQueryCosts
open ThinProductCosts
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
attribute [local irreducible] highTableCap highSumCap highFactor queryFactor

private theorem query_product_identity (P : ℕ) :
    1000000*(64*P^2)^3*(16384*P^3)+1 = 4294967296000000*P^9+1 := by ring

private theorem high_product_identity (P : ℕ) : (2*P)*(4096*P^2) = 8192*P^3 := by ring

theorem highKeyFactor_polynomial (L m : ℕ) :
    HighQueryKeys.queryKeyFactor (2*L) (2*m) ≤ 1024*(L+m+1)^2 := by
  unfold HighQueryKeys.queryKeyFactor HighQueryKeys.physicalFormationWork HighQueryKeys.keyFactor
  ring_nf
  omega

theorem highQueryUnit_polynomial (L m W : ℕ) :
    BinaryHighTable.queryUnit L (2*m) W ≤ 2048*(L+m+W+10)^2 := by
  let U := L+m+W+10
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hU2 : U ≤ U^2 := by nlinarith only [hU]
  have hk : HighQueryKeys.queryKeyFactor (2*L) (2*m) ≤ 1024*U^2 :=
    (highKeyFactor_polynomial L m).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [U]; omega) 2))
  have hs : BackendScalarBits.backendScalarUnit W ≤ 800*U^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_left 800 (Nat.pow_le_pow_left (show W+1≤U by dsimp [U]; omega) 2)
  have hl : 4*L+2*m+8 ≤ 4*U^2 := by
    calc
      _ ≤ 4*U := by dsimp [U]; omega
      _ ≤ _ := Nat.mul_le_mul_left 4 hU2
  unfold BinaryHighTable.queryUnit
  change _ ≤ 2048*U^2
  omega

theorem queryFactor_envelope (L m t q ALeaf : ℕ) (ht : t ≤ 2*m) :
    queryFactor L m t q 1 ALeaf ≤
      2^60*(L+m+q.size+ALeaf.size+(highSumCap L m t q 1).size+10)^9 := by
  let H := highSumCap L m t q 1
  let row := highCoefficientReads m t*highTableCap L m q 1
  let P := L+m+q.size+ALeaf.size+H.size+10
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hP2 : P ≤ P^2 := by nlinarith only [hP]
  have hP2one : 1 ≤ P^2 := Nat.one_le_pow _ _ hP
  have hrow : row.size ≤ H.size := by
    apply Nat.size_le_size
    change row ≤ highSumCap L m t q 1
    unfold highSumCap
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hqp := BinaryLowQuery.queryWidth_polynomial L m (2*m) t q ALeaf
  have hsmall : 2*m+t+2 ≤ 4*P := by dsimp [P]; omega
  have hsquare : 2*(2*m+t+2)^2 ≤ 32*P^2 := by
    exact (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hsmall 2)).trans_eq (by ring)
  have hlinear : 3*(2*m)+3*t+4*m+2*L+2*q.size+2*ALeaf.size+20 ≤ 16*P := by
    dsimp [P]
    omega
  have hlinear2 := hlinear.trans (Nat.mul_le_mul_left 16 hP2)
  have hwidth : BinaryLowQuery.completeWidth L m (2*m) t q ALeaf H+1 ≤ 64*P^2 := by
    have hH : H.size+3 ≤ P := by dsimp [P]; omega
    unfold BinaryLowQuery.completeWidth
    omega
  have hunit : BinaryHighTable.queryUnit L (2*m) row.size ≤ 2048*P^2 :=
    (highQueryUnit_polynomial L m row.size).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [P]; omega) 2))
  have hscalar : BackendScalarBits.backendScalarUnit H.size ≤ 800*P^2 := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_left 800
      (Nat.pow_le_pow_left (show H.size+1≤P by dsimp [P]; omega) 2)
  have hinner : BinaryHighTable.queryUnit L (2*m) row.size+
      BackendScalarBits.backendScalarUnit H.size+10 ≤ 4096*P^2 := by omega
  have hruns : 2*m+1 ≤ 2*P := by dsimp [P]; omega
  have hprod := Nat.mul_le_mul hruns hinner
  have hP3 : 1 ≤ P^3 := Nat.one_le_pow _ _ hP
  have hhigh : highFactor L m t q 1+2 ≤ 16384*P^3 := by
    have heq : (2*P)*(4096*P^2) = 8192*P^3 := high_product_identity P
    rw [heq] at hprod
    unfold highFactor
    change (2*m+1)*(BinaryHighTable.queryUnit L (2*m) row.size+
      BackendScalarBits.backendScalarUnit H.size+10)+1+2 ≤ _
    omega
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hwidth 3)) hhigh
  have hP9 : 1 ≤ P^9 := Nat.one_le_pow _ _ hP
  have hconstant : 4294967296000001 ≤ (2:ℕ)^60 := by norm_num
  change queryFactor L m t q 1 ALeaf ≤ 2^60*P^9
  calc
    _ = 1000000*(BinaryLowQuery.completeWidth L m (2*m) t q ALeaf H+1)^3*
        (highFactor L m t q 1+2)+1 := by unfold queryFactor; rfl
    _ ≤ 1000000*(64*P^2)^3*(16384*P^3)+1 := Nat.add_le_add_right hproduct 1
    _ = 4294967296000000*P^9+1 := query_product_identity P
    _ ≤ 4294967296000001*P^9 := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ hconstant

theorem highReads_le_power (m t : ℕ) (ht : t ≤ 2*m) :
    highCoefficientReads m t ≤ 2^(6*m) := by
  rw [highCoefficientReads_eq]
  calc
    _ ≤ 2^(2*m)*4^t := Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(2*m+2*t) := by rw [show (4:ℕ)=2^2 by norm_num,←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem highTableCap_le_power (L m q r cq : ℕ) (hq : q ≤ 2^(cq*r)) :
    highTableCap L m q 1 ≤ 2^(20*L+2*m+cq*r+3) := by
  have h5 : 5^(2*L+1) ≤ 2^(6*L+3) := by
    calc
      _ ≤ (2^3)^(2*L+1) := Nat.pow_le_pow_left (by norm_num) _
      _ = _ := by rw [←pow_mul]; congr 1; ring
  have hA : (AdaptiveBitBounds.highInputBudget L m 1)^2 = 2^(14*L+2*m) := by
    simp only [AdaptiveBitBounds.highInputBudget,Nat.mul_one,←pow_mul]
    congr 1
    ring
  unfold highTableCap
  rw [hA]
  calc
    _ ≤ 2^(6*L+3)*(2^(cq*r)*2^(14*L+2*m)) := Nat.mul_le_mul h5 (Nat.mul_le_mul_right _ hq)
    _ = _ := by rw [←pow_add,←pow_add]; congr 1; ring

theorem highSumCap_le_power (L m t q r cq : ℕ)
    (ht : t ≤ 2*m) (hq : q ≤ 2^(cq*r)) :
    highSumCap L m t q 1 ≤ 2^(20*L+10*m+cq*r+4) := by
  have hrun : 2*m+1 ≤ 2^(2*m+1) := CoefficientBudget.nat_le_two_pow _
  have hreads := highReads_le_power m t ht
  have hentry := highTableCap_le_power L m q r cq hq
  unfold highSumCap
  calc
    _ ≤ 2^(2*m+1)*(2^(6*m)*2^(20*L+2*m+cq*r+3)) :=
      Nat.mul_le_mul hrun (Nat.mul_le_mul hreads hentry)
    _ = _ := by rw [←pow_add,←pow_add]; congr 1; ring

def querySizeConstant (cL cm cq : ℕ) : ℕ :=
  21*cL+11*cm+2*cq+CoefficientBudget.budgetConstant cL cm cq 0+17
def queryPolylogConstant (cL cm cq : ℕ) : ℕ := 2^60*(querySizeConstant cL cm cq)^9

theorem querySize_le_linear (n L m t q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    L+m+q.size+(CoefficientBounds.uniformBudget L m t q 1).size+
      (highSumCap L m t q 1).size+10 ≤ querySizeConstant cL cm cq*(n.size+1) := by
  let s := n.size+1
  let B := CoefficientBudget.budgetConstant cL cm cq 0
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hl : L ≤ cL*s := hL.trans (Nat.mul_le_mul_left cL (by dsimp [s]; omega))
  have hmi : m ≤ cm*s := hm.trans (Nat.mul_le_mul_left cm (by dsimp [s]; omega))
  have hqsize := (Nat.size_le_size hq).trans_eq Nat.size_pow
  have hq' : q.size ≤ (cq+1)*s := by
    calc
      _ ≤ cq*n.size+1 := hqsize
      _ ≤ cq*s+s := Nat.add_le_add (Nat.mul_le_mul_left cq (by dsimp [s]; omega)) hs
      _ = _ := by ring
  have hleaf := AdaptiveBitBounds.uniformBudget_le_pow_size n 0 L m t q 1 cL cm cq
    hL hm hq (by simp) ht
  have hleafSize := (Nat.size_le_size hleaf).trans_eq Nat.size_pow
  have hleaf' : (CoefficientBounds.uniformBudget L m t q 1).size ≤ (B+1)*s := by
    calc
      _ ≤ B*s+1 := hleafSize
      _ ≤ B*s+s := Nat.add_le_add_left hs _
      _ = _ := by ring
  have hhighSize := (Nat.size_le_size (highSumCap_le_power L m t q n.size cq ht hq)).trans_eq Nat.size_pow
  have hL20 := Nat.mul_le_mul_left 20 hL
  have hm10 := Nat.mul_le_mul_left 10 hm
  have hhigh' : (highSumCap L m t q 1).size ≤ (20*cL+10*cm+cq+5)*s := by
    calc
      _ ≤ 20*L+10*m+cq*n.size+5 := hhighSize
      _ ≤ 20*(cL*n.size)+10*(cm*n.size)+cq*n.size+5 := by omega
      _ = (20*cL+10*cm+cq)*n.size+5 := by ring
      _ ≤ (20*cL+10*cm+cq)*s+5*s := Nat.add_le_add
        (Nat.mul_le_mul_left _ (by dsimp [s]; omega))
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 5 hs)
      _ = _ := by ring
  have h10 : 10 ≤ 10*s := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 10 hs
  change _ ≤ querySizeConstant cL cm cq*s
  calc
    _ ≤ cL*s+cm*s+(cq+1)*s+(B+1)*s+(20*cL+10*cm+cq+5)*s+10*s := by omega
    _ = _ := by unfold querySizeConstant; dsimp [B]; ring

theorem queryFactor_polylog (n L m t q cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    queryFactor L m t q 1 (CoefficientBounds.uniformBudget L m t q 1) ≤
      queryPolylogConstant cL cm cq*(n.size+1)^12 := by
  have he := queryFactor_envelope L m t q (CoefficientBounds.uniformBudget L m t q 1) ht
  have hs := querySize_le_linear n L m t q cL cm cq hL hm hq ht
  have hp := Nat.pow_le_pow_left hs 9
  rw [mul_pow] at hp
  have h9 : (n.size+1)^9 ≤ (n.size+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ 2^60*(L+m+q.size+(CoefficientBounds.uniformBudget L m t q 1).size+
        (highSumCap L m t q 1).size+10)^9 := he
    _ ≤ 2^60*((querySizeConstant cL cm cq)^9*(n.size+1)^9) := Nat.mul_le_mul_left _ hp
    _ ≤ 2^60*((querySizeConstant cL cm cq)^9*(n.size+1)^12) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h9)
    _ = _ := by unfold queryPolylogConstant; rw [Nat.mul_assoc]

#print axioms queryFactor_envelope
#print axioms highSumCap_le_power
#print axioms querySize_le_linear
#print axioms queryFactor_polylog
end ThinMatrix.BinaryQueryCosts


namespace ThinMatrix.BinaryBackendCosts
open ThinMatrixBackend BackendCostRefinement ThinProductCosts
open scoped BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Query price at the actual stored tables, with widths derived from
original zero/one cells. The LOW preparation width W is unrestricted. -/
theorem queryGlobal_price {N D L m t q : ℕ} [NeZero q]
    (B W : ℕ) (shape : ShapePlan L m)
    (left : BinaryBackendExecution.OriginalLeft N D q)
    (right : BinaryBackendExecution.OriginalRight N D q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1)
    (n cL cm cq : ℕ) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m)
    (i j : Fin N) (r : Fin q) :
    (BinaryBackendExecution.queryGlobalExecution (tileWidth_pos L m hmL)
      (BinaryBackendExecution.prepareGlobalShape (t := t) shape W 1 left right) i j r).result.operations ≤
      BinaryQueryCosts.queryPolylogConstant cL cm cq*(n.size+1)^12*
        globalQueryRefinement N L m B*
        (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t) := by
  have hp := BinaryQueryCosts.queryGlobal_cost_original_one B W shape left right hl hr hmL ht i j r
  have hf := BinaryQueryCosts.queryFactor_polylog n L m t q cL cm cq hL hm hq ht
  exact hp.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hf))

def batchConstant (cL cm cq : ℕ) : ℕ :=
  preparationConstant 0 (9*cL+9) (9*cm+9) (9*cq+9)+
    BinaryQueryCosts.queryPolylogConstant cL cm cq

/-- One actual preparation and all the requests against that retained
preparation. The statement does not charge a new preparation per query. -/
theorem prepareGlobal_queries_price {N D L m t q Q : ℕ} [NeZero q]
    (left : BinaryBackendExecution.OriginalLeft N D q)
    (right : BinaryBackendExecution.OriginalRight N D q)
    (requests : Vector (Fin N × Fin N × Fin q) Q)
    (hl : ∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1)
    (hr : ∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1)
    (n cL cm cq B : ℕ) (hn : 1 ≤ n) (hmL : m ≤ L)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) (ht : t ≤ 2*m) :
    let p := BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right
    p.bitSteps+(∑ i : Fin Q, (BinaryBackendExecution.queryGlobalExecution
      (tileWidth_pos L m hmL) p (requests.get i).1 (requests.get i).2.1
        (requests.get i).2.2).result.operations) ≤
      batchConstant cL cm cq*(n.size+1)^12*
        (globalPreparationBudget N L m t q (fullBudget L m q)+
          Q*globalQueryRefinement N L m B*
            (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)) := by
  let p := BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
    (BinaryGeometryWidth.geometryWidth L m q) 1 left right
  let CP := preparationConstant 0 (9*cL+9) (9*cm+9) (9*cq+9)
  let CQ := BinaryQueryCosts.queryPolylogConstant cL cm cq
  let R := (n.size+1)^12
  let P := globalPreparationBudget N L m t q (fullBudget L m q)
  let Z := globalQueryRefinement N L m B*
    (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)
  have hp : p.bitSteps ≤ CP*R*P := prepareGlobal_geometry_price left right hl hr
    n cL cm cq hn hmL hL hm hq ht
  have hquery (i : Fin Q) : (BinaryBackendExecution.queryGlobalExecution
      (tileWidth_pos L m hmL) p (requests.get i).1 (requests.get i).2.1
        (requests.get i).2.2).result.operations ≤ CQ*R*Z := by
    have hc := queryGlobal_price B (BinaryGeometryWidth.geometryWidth L m q)
      (BinaryBackendExecution.prepareShapeRuntime L m) left right hl hr
      n cL cm cq hmL hL hm hq ht (requests.get i).1 (requests.get i).2.1 (requests.get i).2.2
    simpa only [p,BinaryBackendExecution.prepareGlobal,Nat.mul_assoc] using hc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hquery i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  have hcp : CP ≤ CP+CQ := Nat.le_add_right _ _
  have hcq : CQ ≤ CP+CQ := Nat.le_add_left _ _
  have hp' := Nat.mul_le_mul_right P (Nat.mul_le_mul_right R hcp)
  have hq' := Nat.mul_le_mul_left Q (Nat.mul_le_mul_right Z (Nat.mul_le_mul_right R hcq))
  change p.bitSteps+_ ≤ batchConstant cL cm cq*R*(P+Q*globalQueryRefinement N L m B*
    (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t))
  calc
    _ ≤ CP*R*P+Q*(CQ*R*Z) := Nat.add_le_add hp hsum
    _ ≤ (CP+CQ)*R*P+Q*((CP+CQ)*R*Z) := Nat.add_le_add hp' hq'
    _ = _ := by unfold batchConstant; dsimp only [CP,CQ,Z]; ring

theorem computed_cyclic_neZero {n : ℕ}
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    NeZero (call.cyclic AlignedCertificate.S) := by
  have hp : 0 < call.cyclic AlignedCertificate.S := by
    change 0 < (call.factors.drop AlignedCertificate.S).prod
    exact List.prod_pos (fun p hp =>
      (PrimePool.candidate_prime (call.valid p (List.mem_of_mem_drop hp))).pos)
  exact ⟨by omega⟩

def computedBatchConstant : ℕ := batchConstant AdaptiveBitBounds.computedLengthConstant
  AdaptiveBitBounds.computedIndexConstant AdaptiveBitBounds.computedCyclicConstant

attribute [local irreducible] AdaptiveBitBounds.computedLengthConstant
  AdaptiveBitBounds.computedIndexConstant AdaptiveBitBounds.computedCyclicConstant
  computedBatchConstant AlignedCertificate.R AlignedCertificate.S

/-- Computed geometry fixes the actual width and derives every operand cap
for the SAME binary preparation and request family. -/
theorem computed_prepareGlobal_queries_price (n D Q : ℕ) (hn : 3 ≤ n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    letI := computed_cyclic_neZero call
    let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
    let L := ComputableParameters.ordinaryLength m
    let t := ComputableParameters.channelLength m
    let q := call.cyclic AlignedCertificate.S
    let N := PhaseGeometry.outerSize call AlignedCertificate.S n
    ∀ (left : BinaryBackendExecution.OriginalLeft N D q)
      (right : BinaryBackendExecution.OriginalRight N D q)
      (requests : Vector (Fin N × Fin N × Fin q) Q),
    (∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1) →
    (∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1) →
    let p := BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right
    p.bitSteps+(∑ i : Fin Q, (BinaryBackendExecution.queryGlobalExecution
      (tileWidth_pos L m (ComputableParameters.ordinaryLength_lower m)) p
        (requests.get i).1 (requests.get i).2.1 (requests.get i).2.2).result.operations) ≤
      computedBatchConstant*(n.size+1)^12*
        (globalPreparationBudget N L m t q (fullBudget L m q)+
          Q*globalQueryRefinement N L m (BackendNumeratorBounds.numeratorBitBudget L m q 1)*
            (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)) := by
  letI := computed_cyclic_neZero call
  dsimp only
  intro left right requests hl hr
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  have hL : L ≤ AdaptiveBitBounds.computedLengthConstant*n.size := by
    dsimp only [L]
    rw [ComputableParameters.ordinaryLength_eq]
    exact AdaptiveBitBounds.computed_roundedLength_le_size n hn call
  have hm := AdaptiveBitBounds.computed_innerPower_le_size n hn call
  have hq := AdaptiveBitBounds.computed_cyclic_le_pow_size n hn call
  have ht : t ≤ 2*m := by
    dsimp only [t]
    rw [ComputableParameters.channelLength_eq]
    exact AdaptiveBitBounds.rounded_cutoff_le m
  have hp := prepareGlobal_queries_price left right requests hl hr n
    AdaptiveBitBounds.computedLengthConstant AdaptiveBitBounds.computedIndexConstant
    AdaptiveBitBounds.computedCyclicConstant (BackendNumeratorBounds.numeratorBitBudget L m q 1)
    (by omega) (ComputableParameters.ordinaryLength_lower m) hL hm hq ht
  simpa only [computedBatchConstant] using hp

def batchPhaseConstant : ℝ :=
  BinaryPreparationComputed.preparationLogConstant computedBatchConstant*
    BinaryResourcePhase.resourceCoefficient

theorem batchPhaseConstant_nonneg : 0 ≤ batchPhaseConstant := by
  have hresource : 0 ≤ BinaryResourcePhase.resourceCoefficient := by
    unfold BinaryResourcePhase.resourceCoefficient
    exact mul_nonneg
      (mul_nonneg (by norm_num) AlignedAPSPCosts.binaryAllowanceConstant_pos.le)
      (BackendCostRefinement.backendCoefficientConstant_nonneg _ _)
  unfold batchPhaseConstant
  exact mul_nonneg (BinaryPreparationComputed.preparationLogConstant_nonneg _) hresource

/-- The same retained preparation plus at most three requests per original
outer pair is bounded by the six raw phase terms. -/
theorem eventual_prepareGlobal_queries_le_phase :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ call : ComputedPhaseGeometry.Call AlignedCertificate.R n,
      letI := computed_cyclic_neZero call
      let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
      let L := ComputableParameters.ordinaryLength m
      let t := ComputableParameters.channelLength m
      let q := call.cyclic AlignedCertificate.S
      let N := PhaseGeometry.outerSize call AlignedCertificate.S n
      ∀ D Q (left : BinaryBackendExecution.OriginalLeft N D q)
        (right : BinaryBackendExecution.OriginalRight N D q)
        (requests : Vector (Fin N × Fin N × Fin q) Q),
      (∀ i r, (BinaryCell.view ((left.get i).get r)).natAbs ≤ 1) →
      (∀ i r, (BinaryCell.view ((right.get i).get r)).natAbs ≤ 1) →
      Q ≤ 3*n^2 →
      let p := BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
        (BinaryGeometryWidth.geometryWidth L m q) 1 left right
      ((p.bitSteps+(∑ i : Fin Q, (BinaryBackendExecution.queryGlobalExecution
        (tileWidth_pos L m (ComputableParameters.ordinaryLength_lower m)) p
          (requests.get i).1 (requests.get i).2.1 (requests.get i).2.2).result.operations):ℕ):ℝ) ≤
        batchPhaseConstant*(Real.log (n:ℝ))^36*
          ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
            n N ((4:ℝ)^m) q i := by
  filter_upwards [BinaryResourcePhase.eventual_resourceBudget_le_phase,
    Filter.eventually_ge_atTop (3:ℕ)] with n hresource hn
  intro call
  letI := computed_cyclic_neZero call
  dsimp only
  intro D Q left right requests hl hr hQ
  let m := ComputedPhaseGeometry.innerPower n call AlignedCertificate.S
  let L := ComputableParameters.ordinaryLength m
  let t := ComputableParameters.channelLength m
  let q := call.cyclic AlignedCertificate.S
  let N := PhaseGeometry.outerSize call AlignedCertificate.S n
  let P := globalPreparationBudget N L m t q (fullBudget L m q)
  let Z := globalQueryRefinement N L m (BackendNumeratorBounds.numeratorBitBudget L m q 1)*
    (lowCoefficientCost m t q (2*m+1)+highCoefficientReads m t)
  let G := BinaryPreparationComputed.preparationLogConstant computedBatchConstant
  let ell := Real.log (n:ℝ)
  let rawSum := ∑ i : Fin 6, ReductionCosts.rawTerm RealCertificate.c RealCertificate.theta
    n N ((4:ℝ)^m) q i
  let actual := (BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
      (BinaryGeometryWidth.geometryWidth L m q) 1 left right).bitSteps+
      (∑ i : Fin Q, (BinaryBackendExecution.queryGlobalExecution
        (tileWidth_pos L m (ComputableParameters.ordinaryLength_lower m))
        (BinaryBackendExecution.prepareGlobal (L := L) (m := m) (t := t)
          (BinaryGeometryWidth.geometryWidth L m q) 1 left right)
          (requests.get i).1 (requests.get i).2.1 (requests.get i).2.2).result.operations)
  have hb0 := computed_prepareGlobal_queries_price n D Q hn call left right requests hl hr
  have hb : actual ≤ computedBatchConstant*(n.size+1)^12*(P+Q*Z) := by
    simpa only [actual,P,Z,Nat.mul_assoc] using hb0
  have hbudget : P+Q*Z ≤ P+(3*n^2)*Z :=
    Nat.add_le_add_left (Nat.mul_le_mul_right Z hQ) P
  have hb' := hb.trans (Nat.mul_le_mul_left (computedBatchConstant*(n.size+1)^12) hbudget)
  have hlog := BinaryPreparationComputed.naturalFactor_mul_le_logFactor
    computedBatchConstant n ((P+(3*n^2)*Z:ℕ):ℝ) hn (Nat.cast_nonneg _)
  have hbR : (actual:ℝ) ≤
      ((computedBatchConstant*(n.size+1)^12:ℕ):ℝ)*((P+(3*n^2)*Z:ℕ):ℝ) := by
    exact_mod_cast hb'
  have hP : ((P+(3*n^2)*Z:ℕ):ℝ) ≤ BinaryResourcePhase.resourceCoefficient*ell^24*rawSum := by
    simpa only [P,Z,N,L,m,t,q,ell,rawSum,fullBudget,
      BinaryResourcePhase.resourceLogDegree,Nat.mul_assoc] using hresource call
  have hG : 0 ≤ G*ell^12 := by
    exact mul_nonneg (BinaryPreparationComputed.preparationLogConstant_nonneg _)
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _)
  calc
    _ ≤ G*ell^12*((P+(3*n^2)*Z:ℕ):ℝ) := hbR.trans hlog
    _ ≤ G*ell^12*(BinaryResourcePhase.resourceCoefficient*ell^24*rawSum) :=
      mul_le_mul_of_nonneg_left hP hG
    _ = _ := by
      dsimp only [batchPhaseConstant,G,ell,rawSum]
      rw [show (36:ℕ)=12+24 by decide,pow_add]
      ring

#print axioms batchPhaseConstant_nonneg
#print axioms queryGlobal_price
#print axioms prepareGlobal_queries_price
#print axioms computed_prepareGlobal_queries_price
#print axioms eventual_prepareGlobal_queries_le_phase
end
end ThinMatrix.BinaryBackendCosts
