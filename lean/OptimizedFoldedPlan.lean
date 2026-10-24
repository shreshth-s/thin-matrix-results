import FiniteFoldedPlan

set_option autoImplicit false

/-! The exact-half witness's executable ordinary/channel rounding, replacing
the finite L=m,t=0 fallback in the existing typed graph plan. This closes only
those two shape parameters: a supported suffix length, shared production
scheduling, and the complete resource proof remain separate obligations. -/
namespace ThinMatrix.OptimizedFoldedPlan

noncomputable def c : ℝ := 1042290323194818/100000000000000
noncomputable def theta : ℝ := 6568406426999/100000000000000

def ordinaryLength (m : ℕ) : ℕ :=
  (1042290323194818*m+100000000000000-1)/100000000000000

def channelLength (m : ℕ) : ℕ :=
  (13136812853998*m+100000000000000-1)/100000000000000

theorem ordinaryLength_eq (m : ℕ) : ordinaryLength m=Nat.ceil (c*(m:ℝ)) := by
  unfold ordinaryLength
  symm
  convert ComputableParameters.ceilingMulDiv_eq 1042290323194818 m 100000000000000 (by norm_num) using 1
  congr 1
  norm_num [c]
  ring

theorem channelLength_eq (m : ℕ) : channelLength m=Nat.ceil (2*theta*(m:ℝ)) := by
  unfold channelLength
  symm
  convert ComputableParameters.ceilingMulDiv_eq 13136812853998 m 100000000000000 (by norm_num) using 1
  congr 1
  norm_num [theta]
  ring

theorem ordinaryLength_lower (m : ℕ) : m ≤ ordinaryLength m := by
  rw [ordinaryLength_eq]
  have hc : (1:ℝ) ≤ c := by norm_num [c]
  have h : (m:ℝ) ≤ (Nat.ceil (c*(m:ℝ)):ℝ) := by
    calc
      (m:ℝ) ≤ c*(m:ℝ) := by nlinarith
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast h

theorem channelLength_upper (m : ℕ) : channelLength m ≤ m := by
  unfold channelLength
  rw [← Nat.ceilDiv_eq_add_pred_div]
  apply (ceilDiv_le_iff_le_mul (show 0 < (100000000000000:ℕ) by norm_num)).mpr
  nlinarith

theorem rounded_bounds (m : ℕ) :
    c*(m:ℝ) ≤ (ordinaryLength m:ℝ) ∧ (ordinaryLength m:ℝ) < c*(m:ℝ)+1 ∧
    2*theta*(m:ℝ) ≤ (channelLength m:ℝ) ∧ (channelLength m:ℝ) < 2*theta*(m:ℝ)+1 := by
  rw [ordinaryLength_eq,channelLength_eq]
  refine ⟨Nat.le_ceil _,Nat.ceil_lt_add_one ?_,Nat.le_ceil _,Nat.ceil_lt_add_one ?_⟩ <;>
    dsimp only [c,theta] <;> positivity

theorem lengths_zero : ordinaryLength 0=0 ∧ channelLength 0=0 := by
  norm_num [ordinaryLength,channelLength]

theorem channels_pos (m : ℕ) (hm : 0 < m) : 0 < channelLength m := by
  have ht : 0 < (2*theta*(m:ℝ)) := by unfold theta; positivity
  have h := (rounded_bounds m).2.2.1
  have : (0:ℝ) < channelLength m := ht.trans_le h
  exact_mod_cast this

/-- The physical dimensions and fold locations are unchanged. Both shape
lengths are the exact rational witness's upward-rounded values. -/
def produce (n h lowWidth : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    BinaryFoldedFactory.Plan (n:=n) (h:=h) f where
  L := ordinaryLength (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f))
  m := FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f)
  t := channelLength (FoldedBackendExecution.middleExponent h (FoldedBackendExecution.physicalFold f))
  foldWidth := FoldedCounts.foldWidth (FoldedBackendExecution.physicalFold f)
  N := FoldedBackendExecution.outerSize n (FoldedBackendExecution.physicalFold f)
  D := FoldedBackendExecution.middleSize h (FoldedBackendExecution.physicalFold f)
  raw := FoldedBackendExecution.rawMiddle h (FoldedBackendExecution.physicalFold f)
  lowWidth := lowWidth
  foldWidth_eq := rfl
  N_eq := rfl
  D_eq := rfl
  raw_eq := rfl
  m_le_L := ordinaryLength_lower _
  t_le := (channelLength_upper _).trans (by omega)
  middle_fit := le_of_eq (FoldedBackendExecution.middleSize_eq h (FoldedBackendExecution.physicalFold f))

theorem dimensions (n h lowWidth : ℕ) {r : ℕ} (f : CompactBlocks.PhysicalFactorization r) :
    (produce n h lowWidth f).L=Nat.ceil (c*((produce n h lowWidth f).m:ℝ)) ∧
    (produce n h lowWidth f).t=Nat.ceil (2*theta*((produce n h lowWidth f).m:ℝ)) ∧
    (produce n h lowWidth f).D=4^(produce n h lowWidth f).m :=
  ⟨ordinaryLength_eq _,channelLength_eq _,FoldedBackendExecution.middleSize_eq h (FoldedBackendExecution.physicalFold f)⟩

/-- Finite graph semantics are preserved for every suffix parameter. This
alone is not the efficient shared graph schedule. -/
theorem band_count_value {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (lowWidth ell : ℕ) (i : Fin (FoldedBackendExecution.windowQuerySize n)) :
    BinaryCell.view (GraphBandSchedule.output f (produce n h lowWidth f) block input ell i)=
      FoldedRequestBounds.count f block input i :=
  GraphBandSchedule.execute_value f _ block input ell i

#print axioms ordinaryLength_eq
#print axioms channelLength_eq
#print axioms ordinaryLength_lower
#print axioms channelLength_upper
#print axioms rounded_bounds
#print axioms lengths_zero
#print axioms channels_pos
#print axioms dimensions
#print axioms band_count_value
end ThinMatrix.OptimizedFoldedPlan
